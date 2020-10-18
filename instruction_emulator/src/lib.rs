//! A CHIP8 instruction emulator.

use decoder::{decode, Instruction, Operand};
use rand::Rng;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;

/// Abstracts access to the display.
pub trait EmuScreen {
    /// Clears the screen.
    fn clear(&mut self);

    /// Returns the value of a pixel.
    ///
    /// # Arguments
    ///
    /// * `x` - The coordinates on the x-axis
    /// * `y` - The coordinates on the y-axis
    ///
    /// # Returns
    ///
    /// * A `Some` variant that holds the value of a pixel in case of success
    /// * `None` in case of an error
    fn get_pixel(&mut self, x: u8, y: u8) -> Option<u8>;

    /// Sets the value of a pixel.
    ///
    /// # Arguments
    ///
    /// * `x` - The coordinates on the x-axis
    /// * `y` - The coordinates on the y-axis
    /// * `value` - The value of the pixel
    ///
    /// # Returns
    ///
    /// * `Some(())` in case of success
    /// * `None` in case of an error
    fn set_pixel(&mut self, x: u8, y: u8, value: u8) -> Option<()>;
}

/// Describes one of the keys of the CHIP8 keyboard.
#[derive(Clone, Copy)]
pub struct EmuKey(u8);

impl EmuKey {
    pub fn new(key: u8) -> Self {
        assert!(
            key <= 0xf,
            "Key values must be between 0 and 15 (inclusive)!"
        );
        Self(key)
    }
}

/// Abstracts access to the keyboard.
pub trait EmuKeyboard {
    /// Waits until a key is pressend and returns the code of the key.
    fn wait_for_keypress(&mut self) -> EmuKey;

    /// Gets the currenlty pressed key, or `None` if no key is pressed.
    fn get_key(&mut self) -> Option<EmuKey>;
}

/// Abstracts access to memory.
pub trait EmuMemory {
    /// Reads a byte from memory.
    ///
    /// # Arguments
    ///
    /// * `address` - The address from which to read
    ///
    /// # Returns
    ///
    /// * A `Some` variant that holds the value of the byte at `address`
    /// * `None` in case of an error
    fn read(&mut self, address: u16) -> Option<u8>;

    /// Writes a byte to memory.
    ///
    /// # Arguments
    ///
    /// * `address` - The address from which to read
    /// * `value` - The value to be written
    ///
    /// # Returns
    ///
    /// * `Some(())` in case of success
    /// * `None` in case of an error
    fn write(&mut self, address: u16, value: u8) -> Option<()>;
}

/// The register state.
#[derive(Debug, Clone)]
pub struct RegisterState {
    /// The general purpose registers, `V0` through `Ve`.
    gprs: [u8; 15],
    /// The flags register, `Vf`.
    flags: u8,
    /// The address register, `I`.
    address_reg: u16,
    /// The pseudo-register `DT`.
    delay_timer: u8,
    /// The pseudo-register `ST`.
    sound_timer: u8,
    /// The program counter. Points to the currently executing instruction,
    pc: u16,
    /// Stack pointer. Points to the next free stack slot.
    /// This means that when the entire stack is used it will point to an inaccessible slot.
    /// This does not respect the spec, which states that SP points to the topmost stack slot, but it makes pushing and poping easier to reason about.
    sp: u8,
}

impl fmt::Display for RegisterState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for i in 0..15 {
            if i == 8 {
                write!(f, "\n")?;
            }

            write!(f, "V{:x} = {:#04x} ", i, self.gprs[i])?;
        }

        write!(f, "VF = {:#04x}\n", self.flags)?;
        write!(f, "PC = {:#08x} SP = {:#04x}\n", self.pc, self.sp)?;
        write!(f, " I = {:#08x}\n", self.address_reg)?;
        write!(
            f,
            "DT = {:#04x} ST = {:#04x}\n",
            self.delay_timer, self.sound_timer
        )
    }
}

impl Default for RegisterState {
    fn default() -> Self {
        RegisterState {
            gprs: [0; 15],
            flags: 0,
            address_reg: 0,
            delay_timer: 0,
            sound_timer: 0,
            pc: 0x200,
            sp: 0,
        }
    }
}

/// The errors that can be returned from emulation.
#[derive(Debug, PartialEq)]
pub enum EmulationError {
    /// The instruction is not supported by the emulator. Wraps the instruction as decoded by `decoder::decode`.
    InstructionNotSupported(Instruction),
    /// Attempt to emulate an invalid opcode. Wraps the bytes of the instruction in a tuple.
    InvalidOpcode((u8, u8)),
    /// The stack overflowed (`SP` points above the end of the stack).
    StackOverflow,
    /// The stack underflowed (`SP` points below the start of the stack).
    StackUnderFlow,
    /// Attempted to set the value for an operand that can not be set.
    InvalidSetOperandRequest,
    /// Attempted to set a larger value than the operand supports.
    SetOperandValueOverflow,
    /// The program counter overflowed.
    PcOverflow,
    /// Unable to write memory. Wraps the address for which the write failed.
    MemoryWriteError(u16),
    /// Unable to read memory. Wraps the address for which the read failed.
    MemoryReadError(u16),
    /// Unable to render pixel.
    ScreenError,
}

impl fmt::Display for EmulationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EmulationError::InstructionNotSupported(ins) => {
                write!(f, "Instruction not supported: {}", ins)
            }
            EmulationError::InvalidOpcode((u1, u2)) => {
                write!(f, "Invalid opcode: {:02x}{:02x}", u1, u2)
            }
            EmulationError::StackOverflow => write!(f, "Stack overflow"),
            EmulationError::StackUnderFlow => write!(f, "Stack underflow"),
            EmulationError::InvalidSetOperandRequest => write!(f, "Can not set operand"),
            EmulationError::SetOperandValueOverflow => {
                write!(f, "Value too large for given operand")
            }
            EmulationError::PcOverflow => write!(f, "PC underflow"),
            EmulationError::MemoryWriteError(addr) => {
                write!(f, "Unable to write memory address {:#06x}", addr)
            }
            EmulationError::MemoryReadError(addr) => {
                write!(f, "Unable to read memory address {:#06x}", addr)
            }
            EmulationError::ScreenError => write!(f, "Unable to access the screen"),
        }
    }
}

impl Error for EmulationError {}

/// The instruction emulator.
pub struct InstructionEmulator<'a> {
    /// The internal register state.
    register_state: RegisterState,

    /// The stack.
    /// `register_state.sp` points to the next free entry.
    stack: [u16; 16],

    /// Used to draw to the screen.
    screen: &'a mut dyn EmuScreen,

    /// Used to get key press events.
    keyboard: &'a mut dyn EmuKeyboard,

    /// Used to access the memory.
    memory: &'a mut dyn EmuMemory,

    /// Used to control behavior for the `SYS` instruction.
    /// If `true`, the `SYS` instruction is ignored and `PC` is incremented as usual.
    /// If `false`, when a `SYS` instruction is encountered the emulator will return `EmulationError::InstructionNotSupported`.
    /// By default, this is `true`.
    ignore_sys: bool,

    /// Used to trace the emulation.
    /// If `None`, no tracing is done.
    trace_file: Option<File>,
}

impl<'a> InstructionEmulator<'a> {
    /// The size of a font sprite.
    const DEFAULT_FONT_SPRITE_SIZE: u16 = 5;
    /// The base address at which the default font sprites are loaded.
    const DEFAULT_FONT_BASE_ADDRESS: u16 = 0;

    /// Creates a new `InstructionEmulator`.
    ///
    /// The initial registers are all 0.
    ///
    /// # Arguments
    ///
    /// * `screen` - A structure that implements the `EmuScreen` trait. Used to draw to the screen.
    /// * `keyboard` - A structure that implements the `EmuKeyboard` trait. Used to get key press events.
    /// * `memory` - A structure that implements the `EmuMemory` trait. Used to access memory.
    pub fn new(
        screen: &'a mut dyn EmuScreen,
        keyboard: &'a mut dyn EmuKeyboard,
        memory: &'a mut dyn EmuMemory,
    ) -> Self {
        InstructionEmulator::with_initial_state(Default::default(), screen, keyboard, memory, None)
    }

    /// Creates a new `InstructionEmulator` with a given `RegisterState`.
    ///
    /// # Arguments
    ///
    /// * `register_state` - The initial `RegisterState` to be used.
    /// * `screen` - A structure that implements the `EmuScreen` trait. Used to draw to the screen.
    /// * `keyboard` - A structure that implements the `EmuKeyboard` trait. Used to get key press events.
    /// * `memory` - A structure that implements the `EmuMemory` trait. Used to access memory.
    /// * `trace_file` - If `Some`, a file to be used to trace the execution.
    pub fn with_initial_state(
        register_state: RegisterState,
        screen: &'a mut dyn EmuScreen,
        keyboard: &'a mut dyn EmuKeyboard,
        memory: &'a mut dyn EmuMemory,
        trace_file: Option<File>,
    ) -> Self {
        InstructionEmulator {
            register_state,
            stack: Default::default(),
            screen,
            keyboard,
            memory,
            ignore_sys: true,
            trace_file,
        }
    }

    /// Emulates an instruction.
    ///
    /// Will decode and emulate the given instruction. Decoding is done using `decoder::decode`.
    ///
    /// # Arguments
    ///
    /// * `opcode` - The opcode of the instruction that must be emulated.
    ///
    /// # Errors
    ///
    /// Any errors encountered during emulation are reported by returning a `Result` variant that wraps `EmulationError`.
    pub fn emulate(&mut self, opcode: &[u8; 2]) -> Result<(), EmulationError> {
        match decode(opcode) {
            Some(ins) => {
                if let Some(f) = &mut self.trace_file {
                    f.write_fmt(format_args!(
                        "{:05x}: {:02x}{:02x} {}\n{}",
                        self.register_state.pc, opcode[0], opcode[1], ins, self.register_state
                    ))
                    .unwrap();
                }
                self.emulate_instruction(ins)
            }
            None => Err(EmulationError::InvalidOpcode((opcode[0], opcode[1]))),
        }
    }

    /// Emulates an already decoded instruction.
    ///
    /// # Arguments
    ///
    /// * `instruction` - The instruction that must be emulated.
    ///
    /// # Errors
    ///
    /// Any errors encountered during emulation are reported by returning a `Result` variant that wraps `EmulationError`.
    pub fn emulate_instruction(&mut self, instruction: Instruction) -> Result<(), EmulationError> {
        if self.emulate_internal(instruction)? {
            self.register_state.pc += 2;
        }

        Ok(())
    }

    /// Fetches the next instruction from memory and emulates it.
    ///
    /// # Errors
    ///
    /// Any errors encountered during emulation are reported by returning a `Result` variant that wraps `EmulationError`.
    pub fn emulate_next(&mut self) -> Result<(), EmulationError> {
        // Fetch the instruction at `PC`. The instruction is always 2 bytes long.
        let pc = self.register_state.pc;
        let code: [u8; 2] = [
            self.memory
                .read(pc)
                .ok_or(EmulationError::MemoryReadError(pc))?,
            self.memory
                .read(pc + 1)
                .ok_or(EmulationError::MemoryReadError(pc + 1))?,
        ];
        // Emulate. This will advance `PC` as needed.
        self.emulate(&code)
    }

    /// Returns a copy of the current register state.
    pub fn get_register_state(&self) -> RegisterState {
        self.register_state.clone()
    }

    // Decrements the timers if needed.
    pub fn decrement_timers(&mut self) {
        if self.register_state.delay_timer > 0 {
            self.register_state.delay_timer -= 1;
        }

        if self.register_state.sound_timer > 0 {
            self.register_state.sound_timer -= 1;
        }
    }

    /// Emulates an already decoded instruction.
    /// This function will not advance the program counter past the current instruction. If `PC` needs to be advanced this function returns `Ok(true)`, otherwise it returns `Ok(false)`.
    ///
    /// # Arguments
    ///
    /// * `instruction` - The instruction that must be emulated.
    ///
    /// # Errors
    ///
    /// Any errors encountered during emulation are reported by returning a `Result` variant that wraps `EmulationError`.
    fn emulate_internal(&mut self, instruction: Instruction) -> Result<bool, EmulationError> {
        // See http://www.cs.columbia.edu/~sedwards/classes/2016/4840-spring/reports/Chip8.pdf

        match instruction {
            Instruction::Sys(_) => {
                if self.ignore_sys {
                    Ok(true)
                } else {
                    Err(EmulationError::InstructionNotSupported(instruction))
                }
            }
            Instruction::Cls => {
                self.screen.clear();
                Ok(true)
            }
            Instruction::Ret => {
                // Set the program counter.
                self.register_state.pc = self.pop_stack()?;

                // Don't update PC again.
                Ok(false)
            }
            Instruction::Jp((op1, op2)) => {
                match op2 {
                    Some(op2) => {
                        // This is the version with two operands.

                        // Make sure the first operand is register V0.
                        assert!(
                            op1 == Operand::Gpr(0),
                            "Invalid Vx encoding for `JP V0, addr`!"
                        );

                        // Get the value of V0.
                        let v0 = self.register_state.gprs[0];

                        // Get the address from the second operand.
                        let address = self.get_operand_value(&op2);

                        // Set the program counter.
                        self.register_state.pc = (v0 as u16)
                            .checked_add(address)
                            .ok_or(EmulationError::PcOverflow)?;

                        // Don't update PC again.
                        Ok(false)
                    }
                    None => {
                        // This is the version with a single operand.

                        // Set the program counter.
                        self.register_state.pc = self.get_operand_value(&op1);

                        // Don't update PC again.
                        Ok(false)
                    }
                }
            }
            Instruction::Call(op) => {
                // Save the next program counter on the stack.
                self.push_stack(self.register_state.pc + 2)?;

                // Set the program counter.
                self.register_state.pc = self.get_operand_value(&op);

                // Don't update PC again.
                Ok(false)
            }
            Instruction::Se((op1, op2)) => {
                // Get the value of the first operand.
                let lhs = self.get_operand_value(&op1);

                // Get the value of the second operand.
                let rhs = self.get_operand_value(&op2);

                assert!(lhs <= 0xFF, "Operand 1 for `SE` does not fit in 8 bits!");
                assert!(rhs <= 0xFF, "Operand 2 for `SE` does not fit in 8 bits!");

                if lhs == rhs {
                    // Skip the next instruction.
                    self.register_state.pc += 2;
                }

                // Update PC.
                // This is OK because in the skipped case we only increment PC by 2.
                Ok(true)
            }
            Instruction::Sne((op1, op2)) => {
                // Get the value of the first operand.
                let lhs = self.get_operand_value(&op1);

                // Get the value of the second operand.
                let rhs = self.get_operand_value(&op2);

                assert!(lhs <= 0xFF, "Operand 1 for `SE` does not fit in 8 bits!");
                assert!(rhs <= 0xFF, "Operand 2 for `SE` does not fit in 8 bits!");

                if lhs != rhs {
                    // Skip the next instruction.
                    self.register_state.pc += 2;
                }

                // Update PC.
                // This is OK because in the skipped case we only increment PC by 2.
                Ok(true)
            }
            Instruction::Ld((op1, op2)) => {
                if let Operand::Memory = op1 {
                    // Special case for LD [I], Vx.
                    self.store_gprs_to_memory(op2)?;
                } else if let Operand::Memory = op2 {
                    // Special case for LD Vx, [I].
                    self.load_gprs_from_memory(op1)?;
                } else if let Operand::Key = op2 {
                    // Special case for LD Vx, K.
                    let k = self.keyboard.wait_for_keypress().0 as u16;
                    self.set_operand_value(&op1, k)?;
                } else if let Operand::Font = op1 {
                    // Special case for LD F, Vx.
                    let index = self.get_operand_value(&op2);

                    // Compute the address of the sprite and store it in the `I` register.
                    self.register_state.address_reg =
                        Self::DEFAULT_FONT_BASE_ADDRESS + index * Self::DEFAULT_FONT_SPRITE_SIZE;
                } else if let Operand::Bcd = op1 {
                    // Special case for LD B, Vx.
                    // Store the digits of `Vx` in memory at `I`, `I + 1`, `I + 2`.
                    let value = self.get_operand_value(&op2) as u8;

                    let base_address = self.register_state.address_reg;

                    self.memory
                        .write(base_address, value / 100)
                        .ok_or(EmulationError::MemoryWriteError(base_address))?;
                    self.memory
                        .write(base_address + 1, value % 100 / 10)
                        .ok_or(EmulationError::MemoryWriteError(base_address + 1))?;
                    self.memory
                        .write(base_address + 2, value % 100 % 10)
                        .ok_or(EmulationError::MemoryWriteError(base_address + 2))?;
                } else {
                    // All the other cases.
                    // Set the first operand to the value of the second operand.
                    self.set_operand_value(&op1, self.get_operand_value(&op2))?;
                }

                // Update PC.
                Ok(true)
            }
            Instruction::Add((op1, op2)) => {
                // Get the value of the first operand.
                let lhs: u16 = self.get_operand_value(&op1);

                // Get the value of the second operand.
                let rhs: u16 = self.get_operand_value(&op2);

                let mut result = lhs + rhs;

                // If the first operand is a register, check if the result fits into 8 bits.
                if Self::is_operand_gpr(&op1) {
                    if result <= 0xFF {
                        // Store it as it is and clear VF.
                        self.register_state.flags = 0;
                    } else {
                        // Keep only the low 8 bits and set VF.
                        result &= 0xFF;
                        self.register_state.flags = 1;
                    }
                } else {
                    // TODO: should VF be reset here?
                    self.register_state.flags = 0;
                }

                // Store the result.
                self.set_operand_value(&op1, result)?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Or((op1, op2)) => {
                // op1 = op1 | op2.
                self.set_operand_value(
                    &op1,
                    self.get_operand_value(&op1) | self.get_operand_value(&op2),
                )?;

                // Increment PC.
                Ok(true)
            }
            Instruction::And((op1, op2)) => {
                // op1 = op1 & op2.
                self.set_operand_value(
                    &op1,
                    self.get_operand_value(&op1) & self.get_operand_value(&op2),
                )?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Xor((op1, op2)) => {
                // op1 = op1 ^ op2.
                self.set_operand_value(
                    &op1,
                    self.get_operand_value(&op1) ^ self.get_operand_value(&op2),
                )?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Sub((op1, op2)) => {
                // Get the value of the first operand.
                let lhs = self.get_operand_value(&op1) as u8;

                // Get the value of the second operand.
                let rhs = self.get_operand_value(&op2) as u8;

                if lhs > rhs {
                    // Set VF.
                    self.register_state.flags = 1;
                } else {
                    // Clear VF.
                    self.register_state.flags = 0;
                }

                // op1 = op1 - op2.
                self.set_operand_value(&op1, lhs.wrapping_sub(rhs) as u16)?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Shr((op1, _op2)) => {
                // TODO: The instruction encodes two operands, but it seems that only the first matters.
                let val = self.get_operand_value(&op1) as u8;

                if (val & 0x1) != 0 {
                    // Set VF.
                    self.register_state.flags = 1;
                } else {
                    // Clear VF.
                    self.register_state.flags = 0;
                }

                // op1 = op1 >> 1
                self.set_operand_value(&op1, (val >> 1) as u16)?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Subn((op1, op2)) => {
                // Get the value of the first operand.
                let lhs = self.get_operand_value(&op1) as u8;

                // Get the value of the second operand.
                let rhs = self.get_operand_value(&op2) as u8;

                if lhs < rhs {
                    // Set VF.
                    self.register_state.flags = 1;
                } else {
                    // Clear VF.
                    self.register_state.flags = 0;
                }

                // op1 = op2 - op1.
                self.set_operand_value(&op1, rhs.wrapping_sub(lhs) as u16)?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Shl((op1, _op2)) => {
                // TODO: The instruction encodes two operands, but it seems that only the first matters.
                let val = self.get_operand_value(&op1) as u8;

                if (val & 0x80) != 0 {
                    // Set VF.
                    self.register_state.flags = 1;
                } else {
                    // Clear VF.
                    self.register_state.flags = 0;
                }

                // op1 = op1 << 1
                self.set_operand_value(&op1, (val << 1) as u16)?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Rnd((op1, op2)) => {
                // op1 = random & op2
                self.set_operand_value(
                    &op1,
                    (Self::get_random_u8() & self.get_operand_value(&op2) as u8) as u16,
                )?;

                // Increment PC.
                Ok(true)
            }
            Instruction::Drw((op1, op2, op3)) => {
                // Get the x and y coordinates and the number of bytes this sprite has.
                let x = self.get_operand_value(&op1) as u8;
                let y = self.get_operand_value(&op2) as u8;
                let n = self.get_operand_value(&op3) as u8;

                self.draw_sprite(x, y, n)?;

                // Advance PC.
                Ok(true)
            }
            Instruction::Skp(op) => {
                // Get the expected key value.
                let expected_key = self.get_operand_value(&op) as u8;

                // If a key was pressed.
                if let Some(key) = self.keyboard.get_key() {
                    // And it is the key we are waiting for.
                    if expected_key == key.0 {
                        // Skip the next instruction.
                        self.register_state.pc += 2;
                    }
                }

                // Update PC.
                // This is OK because in the skipped case we only increment PC by 2.
                Ok(true)
            }
            Instruction::Sknp(op) => {
                // Get the expected key value.
                let expected_key = self.get_operand_value(&op) as u8;

                // If a key was pressed
                if let Some(key) = self.keyboard.get_key() {
                    // And it is not our key.
                    if expected_key != key.0 {
                        // Skip the next instruction.
                        self.register_state.pc += 2;
                    }
                } else {
                    // If no key was pressed we also skip the next instruction.
                    self.register_state.pc += 2;
                }

                // Update PC.
                // This is OK because in the skipped case we only increment PC by 2.
                Ok(true)
            }
        }
    }

    /// Returns the value of an operand.
    ///
    /// # Arguments
    ///
    /// * `op` - The operand for which to return a value.
    ///
    /// # Remarks
    ///
    /// This function always returns the value as a `u16`, even for operands that wrap smaller values.
    ///
    /// # Errors
    ///
    /// For operands that do not support this operation the function panics. These operands are:
    ///
    /// * `Operand::Memory`
    /// * `Operand::Key`
    /// * `Operand::Font`
    /// * `Operand::Bcd`
    fn get_operand_value(&self, op: &Operand) -> u16 {
        match *op {
            Operand::Address(address) => {
                assert!(
                    (address & 0x0FFF) == address,
                    "get_operand: Address has more than 12 bits set!"
                );
                address
            }
            Operand::Gpr(index) => {
                assert!(
                    (index as usize) < self.register_state.gprs.len(),
                    "get_operand: GPR index out of bounds!"
                );
                self.register_state.gprs[index as usize] as u16
            }
            Operand::Flags => self.register_state.flags as u16,
            Operand::Byte(value) => value as u16,
            Operand::Nibble(value) => {
                assert!(
                    value <= 0xF,
                    "get_operand: Nibble value does not fit in 4 bits!"
                );
                value as u16
            }
            Operand::AddrReg => {
                assert!(
                    (self.register_state.address_reg & 0x0FFF) == self.register_state.address_reg,
                    "get_operand: I register has more than 12 bits set!"
                );
                self.register_state.address_reg
            }
            Operand::Memory => unreachable!(),
            Operand::DelayTimer => self.register_state.delay_timer as u16,
            Operand::SoundTimer => self.register_state.sound_timer as u16,
            Operand::Key => unreachable!(),
            Operand::Font => unreachable!(),
            Operand::Bcd => unreachable!(),
        }
    }

    /// Sets the value of an operand.
    ///
    /// # Arguments
    ///
    /// * `op` - The operand for which to return a value
    /// * `value` - The new operand value
    ///
    /// # Remarks
    ///
    /// This function always takes the new value as a `u16`, even for operands that wrap smaller values.
    ///
    /// # Errors
    ///
    /// If `value` does not fit inside the given operand the function returns `EmulationError::SetOperandValueOverflow`.
    /// For operands that do not support this operation the function returns `EmulationError::InvalidSetOperandRequest`. These operands are:
    ///
    /// * `Operand::Memory`
    /// * `Operand::Key`
    /// * `Operand::Font`
    /// * `Operand::Bcd`
    fn set_operand_value(&mut self, op: &Operand, value: u16) -> Result<(), EmulationError> {
        match *op {
            Operand::Address(_) => Err(EmulationError::InvalidSetOperandRequest),
            Operand::Gpr(index) => {
                assert!(
                    (index as usize) < self.register_state.gprs.len(),
                    "set_operand: GPR index out of bounds!"
                );
                if (value & 0xFF) != value {
                    Err(EmulationError::SetOperandValueOverflow)
                } else {
                    self.register_state.gprs[index as usize] = value as u8;
                    Ok(())
                }
            }
            Operand::Flags => {
                if (value & 0xFF) != value {
                    Err(EmulationError::SetOperandValueOverflow)
                } else {
                    self.register_state.flags = value as u8;
                    Ok(())
                }
            }
            Operand::Byte(_) => Err(EmulationError::InvalidSetOperandRequest),
            Operand::Nibble(_) => Err(EmulationError::InvalidSetOperandRequest),
            Operand::AddrReg => {
                if (value & 0x0FFF) != value {
                    Err(EmulationError::SetOperandValueOverflow)
                } else {
                    self.register_state.address_reg = value;
                    Ok(())
                }
            }
            Operand::Memory => unreachable!(),
            Operand::DelayTimer => {
                if (value & 0xFF) != value {
                    Err(EmulationError::SetOperandValueOverflow)
                } else {
                    self.register_state.delay_timer = value as u8;
                    Ok(())
                }
            }
            Operand::SoundTimer => {
                if (value & 0xFF) != value {
                    Err(EmulationError::SetOperandValueOverflow)
                } else {
                    self.register_state.sound_timer = value as u8;
                    Ok(())
                }
            }
            Operand::Key => Err(EmulationError::InvalidSetOperandRequest),
            Operand::Font => Err(EmulationError::InvalidSetOperandRequest),
            Operand::Bcd => Err(EmulationError::InvalidSetOperandRequest),
        }
    }

    /// Handles `Fx55`: `LD [I], Vx`.
    ///
    /// # Arguments
    ///
    /// - `op` - The operand that describes the last register to store (esentially it is `Vx`).
    ///
    /// # Errors
    ///
    /// If memory can not be written returns an `EmulationError::MemoryWriteError` that wraps the address for which the write failed.
    ///
    /// If `op` is not `Operand::Gpr` or `Operand::Flags` the function panics.
    fn store_gprs_to_memory(&mut self, op: Operand) -> Result<(), EmulationError> {
        // Store registers `V0 `through `Vx` into memory starting at location held by `I`.
        // `I` is not incremented.

        // Get the starting address.
        let base_address = self.register_state.address_reg;

        // Get the index of the upper register.
        let index = match op {
            Operand::Gpr(i) => i,
            Operand::Flags => 15,
            _ => unreachable!(),
        };

        assert!(
            index <= 0xF,
            "Invalid `Vx` index when storing registers into memory!"
        );

        // Go through all the registers, starting from `V0`.
        // Because we represent `VF` as a dedicated register we write the last one at the end.
        for i in 0..index {
            self.memory
                .write(
                    base_address + i as u16,
                    self.register_state.gprs[i as usize],
                )
                .ok_or(EmulationError::MemoryWriteError(base_address + i as u16))?;
        }

        // Check if we should also write `VF`.
        if index == 0xf {
            self.memory
                .write(base_address + index as u16, self.register_state.flags)
                .ok_or(EmulationError::MemoryWriteError(
                    base_address + index as u16,
                ))?;
        } else {
            // Just a GPR.
            self.memory
                .write(
                    base_address + index as u16,
                    self.register_state.gprs[index as usize],
                )
                .ok_or(EmulationError::MemoryWriteError(
                    base_address + index as u16,
                ))?;
        }

        Ok(())
    }

    /// Handles `Fx65`: `LD Vx, [I]`
    ///
    /// # Arguments
    ///
    /// - `op` - The operand that describes the last register to load (esentially it is `Vx`).
    ///
    /// # Errors
    ///
    /// If memory can not be read returns an `EmulationError::MemoryReadError` that wraps the address for which the read failed.
    ///
    /// If `op` is not `Operand::Gpr` or `Operand::Flags` the function panics.
    fn load_gprs_from_memory(&mut self, op: Operand) -> Result<(), EmulationError> {
        // Load registers `V0 `through `Vx` into memory starting at location held by `I`.
        // `I` is not incremented.

        // Get the starting address.
        let base_address = self.register_state.address_reg;

        // Get the index of the upper register.
        let index = match op {
            Operand::Gpr(i) => i,
            Operand::Flags => 15,
            _ => unreachable!(),
        };

        assert!(
            index <= 0xF,
            "Invalid `Vx` index when loading registers from memory!"
        );

        // Go through all the registers, starting from `V0`.
        // Because we represent `VF` as a dedicated register we read the last one at the end.
        for i in 0..index {
            self.register_state.gprs[i as usize] = self
                .memory
                .read(base_address + i as u16)
                .ok_or(EmulationError::MemoryReadError(base_address + i as u16))?;
        }

        // Check if we should also load `VF`.
        if index == 0xf {
            self.register_state.flags = self
                .memory
                .read(base_address + index as u16)
                .ok_or(EmulationError::MemoryReadError(base_address + index as u16))?;
        } else {
            // Just a GPR.
            self.register_state.gprs[index as usize] = self
                .memory
                .read(base_address + index as u16)
                .ok_or(EmulationError::MemoryReadError(base_address + index as u16))?;
        }

        Ok(())
    }

    /// Reads and draws a sprite.
    ///
    /// # Arguments
    ///
    /// * `x` - The x-axis coordinates at which the drawing starts
    /// * `y` - The y-axis coordinates at which the draeing starts
    /// * `count` - The number of bytes to read for the sprite
    ///
    /// # Returns
    ///
    /// * `Ok(())` in case of success
    /// * `EmulationError::ScreenError` in case of error
    fn draw_sprite(&mut self, x: u8, y: u8, count: u8) -> Result<(), EmulationError> {
        // See https://stackoverflow.com/questions/17346592/how-does-chip-8-graphics-rendered-on-screen
        // and http://craigthomas.ca/blog/2015/02/19/writing-a-chip-8-emulator-draw-command-part-3/.

        let base_address = self.register_state.address_reg;

        // Starting from `I`, read `count` bytes of memory. These bytes represent a sprite.
        for i in 0..count {
            let sprite_byte = self
                .memory
                .read(base_address + i as u16)
                .ok_or(EmulationError::MemoryWriteError(base_address + i as u16))?;

            // Coordinates on the y axis.
            let y_pos = y + i;

            // Process this byte.
            self.draw_sprite_byte(x, y_pos, sprite_byte)?;
        }

        Ok(())
    }

    /// Draws a sprite.
    ///
    /// # Arguments
    ///
    /// * `x` - The x-axis coordinates at which the drawing starts
    /// * `y` - The y-axis coordinates at which the draeing starts
    /// * `count` - The number of bytes to read for the sprite
    ///
    /// # Returns
    ///
    /// * `Ok(())` in case of success
    /// * `EmulationError::ScreenError` in case of error
    fn draw_sprite_byte(&mut self, x: u8, y: u8, sprite_byte: u8) -> Result<(), EmulationError> {
        let mut sprite_byte = sprite_byte;
        for b in 0..8 {
            // Coordinates on the x axis.
            let x_pos = x + b;

            // Get the current value of the pixel.
            let old_pixel = self
                .screen
                .get_pixel(x_pos, y)
                .ok_or(EmulationError::ScreenError)?;

            // Compute the new value.
            let val = (sprite_byte & 0x80) != 0;
            let new_pixel = old_pixel ^ val as u8;

            // If we turned the pixel off set `VF`.
            if old_pixel == 1 && new_pixel == 0 {
                self.register_state.flags = 1;
            }

            // Write it.
            self.screen
                .set_pixel(x_pos, y, new_pixel)
                .ok_or(EmulationError::ScreenError)?;

            // Advance to the next pixel.
            sprite_byte <<= 1;
        }

        Ok(())
    }

    /// Pushes a value onto the stack.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be written on the stack.
    ///
    /// # Remarks
    ///
    /// The order of operation is reversed when compared to the specs: first, `value` is written to `stack[SP]`, then `SP` is incremented.
    ///
    /// # Errors
    ///
    /// `EmulationError::StackUnderFlow` if `SP` overflows.
    fn push_stack(&mut self, value: u16) -> Result<(), EmulationError> {
        // Make sure SP isn't something crazy.
        assert!(
            (self.register_state.sp as usize) < self.stack.len(),
            "SP points outisde the stack before push!"
        );

        // Save the value on the stack.
        self.stack[self.register_state.sp as usize] = value;

        // Increment SP.
        // The spec says that SP is first incremented, then the value is written at `stack[SP]`, but if we do the increment
        // before the write when SP is 0 we will never use `stack[0]`. This means that `SP` no longer points to the last used
        // slot of the stack, but to the next free one.
        self.register_state.sp = self
            .register_state
            .sp
            .checked_add(1)
            .ok_or(EmulationError::StackOverflow)?;

        Ok(())
    }

    /// Pops a value from the stack.
    ///
    /// # Remarks
    ///
    /// The order of operation is reversed when compared to the specs: first, `SP` is decremented, then the value is read from `stack[SP]`.
    ///
    /// # Errors
    ///
    /// `EmulationError::StackUnderFlow` if `SP` underflows.
    fn pop_stack(&mut self) -> Result<u16, EmulationError> {
        // Decrement SP.
        // The spec says that SP is decremented after the value is read from the stack, but because we reversed the order of operations
        // in `push_stack` we have to also revere it here.
        self.register_state.sp = self
            .register_state
            .sp
            .checked_sub(1)
            .ok_or(EmulationError::StackUnderFlow)?;

        // Make sure SP isn't something crazy.
        assert!(
            (self.register_state.sp as usize) < self.stack.len(),
            "SP points outisde the stack after pop!"
        );

        // Get the value.
        let value = self.stack[self.register_state.sp as usize];

        Ok(value)
    }

    /// Returns `true` if a `decoder::Operand` is `Operand::Gpr`.
    fn is_operand_gpr(op: &Operand) -> bool {
        match op {
            Operand::Gpr(_) => true,
            _ => false,
        }
    }

    /// Returns a random `u8` value.
    fn get_random_u8() -> u8 {
        rand::thread_rng().gen()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestScreen;
    struct TestKeyboard;
    struct TestMemory;

    impl EmuScreen for TestScreen {
        fn clear(&mut self) {}
        fn get_pixel(&mut self, _x: u8, _y: u8) -> Option<u8> {
            Some(0)
        }
        fn set_pixel(&mut self, _x: u8, _y: u8, _pixel: u8) -> Option<()> {
            Some(())
        }
    }

    impl EmuKeyboard for TestKeyboard {
        fn wait_for_keypress(&mut self) -> EmuKey {
            EmuKey::new(0)
        }

        fn get_key(&mut self) -> Option<EmuKey> {
            None
        }
    }

    impl EmuMemory for TestMemory {
        fn read(&mut self, _address: u16) -> Option<u8> {
            Some(0)
        }
        fn write(&mut self, _address: u16, _value: u8) -> Option<()> {
            Some(())
        }
    }

    #[test]
    fn stack() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        // We should be able to push 16 values.
        for i in 0..16 {
            emu.push_stack(i as u16).unwrap();
        }

        // And then pop those values.
        for i in 15..=0 {
            assert_eq!(emu.pop_stack().unwrap(), i as u16);
        }
    }

    #[test]
    #[should_panic]
    fn stack_pop_sp_outside() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.sp = emu.stack.len() as u8 + 1;
        emu.pop_stack().unwrap();
    }

    #[test]
    #[should_panic]
    fn stack_push_sp_outside() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.sp = emu.stack.len() as u8;
        emu.push_stack(0).unwrap();
    }

    #[test]
    fn get_operand_value() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        assert_eq!(emu.get_operand_value(&Operand::Address(0xabc)), 0xabc);

        for i in 0..emu.register_state.gprs.len() {
            emu.register_state.gprs[i] = i as u8;

            assert_eq!(emu.get_operand_value(&Operand::Gpr(i as u8)), i as u16);
        }

        emu.register_state.flags = 2;
        assert_eq!(emu.get_operand_value(&Operand::Flags), 2);

        assert_eq!(emu.get_operand_value(&Operand::Byte(0xff)), 0xff);

        assert_eq!(emu.get_operand_value(&Operand::Nibble(0xf)), 0xf);

        emu.register_state.address_reg = 0x123;
        assert_eq!(emu.get_operand_value(&Operand::AddrReg), 0x123);

        emu.register_state.delay_timer = 0x23;
        assert_eq!(emu.get_operand_value(&Operand::DelayTimer), 0x23);

        emu.register_state.sound_timer = 0x34;
        assert_eq!(emu.get_operand_value(&Operand::SoundTimer), 0x34);
    }

    #[test]
    fn set_operand_value() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        for i in 0..emu.register_state.gprs.len() {
            emu.register_state.gprs[i] = i as u8;

            emu.set_operand_value(&Operand::Gpr(i as u8), i as u16)
                .unwrap();
            assert_eq!(emu.register_state.gprs[i], i as u8);
        }

        emu.set_operand_value(&Operand::Flags, 2).unwrap();
        assert_eq!(emu.register_state.flags, 2);

        emu.set_operand_value(&Operand::AddrReg, 0xabc).unwrap();
        assert_eq!(emu.register_state.address_reg, 0xabc);

        emu.set_operand_value(&Operand::DelayTimer, 0x56).unwrap();
        assert_eq!(emu.register_state.delay_timer, 0x56);

        emu.set_operand_value(&Operand::SoundTimer, 0x67).unwrap();
        assert_eq!(emu.register_state.sound_timer, 0x67);

        assert_eq!(
            emu.set_operand_value(&Operand::Address(0), 0).unwrap_err(),
            EmulationError::InvalidSetOperandRequest
        );
        assert_eq!(
            emu.set_operand_value(&Operand::Byte(0), 0).unwrap_err(),
            EmulationError::InvalidSetOperandRequest
        );
        assert_eq!(
            emu.set_operand_value(&Operand::Nibble(0), 0).unwrap_err(),
            EmulationError::InvalidSetOperandRequest
        );

        assert_eq!(
            emu.set_operand_value(&Operand::Gpr(0), 0x123).unwrap_err(),
            EmulationError::SetOperandValueOverflow
        );
        assert_eq!(
            emu.set_operand_value(&Operand::DelayTimer, 0x123)
                .unwrap_err(),
            EmulationError::SetOperandValueOverflow
        );
        assert_eq!(
            emu.set_operand_value(&Operand::SoundTimer, 0x123)
                .unwrap_err(),
            EmulationError::SetOperandValueOverflow
        );
        assert_eq!(
            emu.set_operand_value(&Operand::AddrReg, 0x1f00)
                .unwrap_err(),
            EmulationError::SetOperandValueOverflow
        );
    }

    #[test]
    fn emulate_sys() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.ignore_sys = false;
        assert_eq!(
            emu.emulate_internal(Instruction::Sys(Operand::Address(0)))
                .unwrap_err(),
            EmulationError::InstructionNotSupported(Instruction::Sys(Operand::Address(0)))
        );

        emu.ignore_sys = true;
        assert_eq!(
            emu.emulate_internal(Instruction::Sys(Operand::Address(0)))
                .unwrap(),
            true
        );
    }

    #[test]
    fn emulate_ret() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        // Make sure we have something on the stack.
        emu.push_stack(0x123).unwrap();

        assert_eq!(emu.emulate_internal(Instruction::Ret).unwrap(), false);
        assert_eq!(emu.register_state.pc, 0x123);
        assert_eq!(emu.register_state.sp, 0);
    }

    #[test]
    fn emulate_jp() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        // One operand version.
        assert_eq!(
            emu.emulate_internal(Instruction::Jp((Operand::Address(0x100), None)))
                .unwrap(),
            false
        );
        assert_eq!(emu.register_state.pc, 0x100);

        // Two operand version.
        emu.register_state.gprs[0] = 0x10;
        assert_eq!(
            emu.emulate_internal(Instruction::Jp((
                Operand::Gpr(0),
                Some(Operand::Address(0x200))
            )))
            .unwrap(),
            false
        );
        assert_eq!(emu.register_state.pc, 0x210);
    }

    #[test]
    fn emulate_call() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.pc = 0x100;

        assert_eq!(
            emu.emulate_internal(Instruction::Call(Operand::Address(0x200)))
                .unwrap(),
            false
        );
        assert_eq!(emu.register_state.pc, 0x200);
        assert_eq!(emu.register_state.sp, 1);
        assert_eq!(emu.stack[0], 0x102);
    }

    #[test]
    fn emulate_se() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.pc = 0x100;
        emu.register_state.gprs[0] = 1;
        emu.register_state.gprs[1] = 1;

        assert_eq!(
            emu.emulate_internal(Instruction::Se((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x102);

        emu.register_state.pc = 0x100;
        emu.register_state.gprs[0] = 2;

        assert_eq!(
            emu.emulate_internal(Instruction::Se((Operand::Gpr(0), Operand::Byte(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x100);
    }

    #[test]
    fn emulate_sne() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.pc = 0x100;
        emu.register_state.gprs[0] = 1;
        emu.register_state.gprs[1] = 1;

        assert_eq!(
            emu.emulate_internal(Instruction::Sne((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x100);

        emu.register_state.pc = 0x100;
        emu.register_state.gprs[0] = 2;

        assert_eq!(
            emu.emulate_internal(Instruction::Sne((Operand::Gpr(0), Operand::Byte(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x102);
    }

    #[test]
    fn emulate_ld() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        // LD Vx, byte
        emu.register_state.gprs[0] = 0;
        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Gpr(0), Operand::Byte(2))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 2);

        // LD Vx, Vy
        emu.register_state.gprs[0] = 0;
        emu.register_state.gprs[1] = 1;
        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 1);

        // LD I, addr
        emu.register_state.address_reg = 0;
        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::AddrReg, Operand::Address(0x200))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.address_reg, 0x200);

        // LD Vx, DT
        emu.register_state.gprs[0] = 0;
        emu.register_state.delay_timer = 10;
        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Gpr(0), Operand::DelayTimer)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 10);

        // LD DT, Vx
        emu.register_state.delay_timer = 0;
        emu.register_state.gprs[1] = 12;
        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::DelayTimer, Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.delay_timer, 12);

        // LD Vx, ST
        emu.register_state.gprs[0] = 0;
        emu.register_state.sound_timer = 16;
        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Gpr(0), Operand::SoundTimer)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 16);

        // LD ST, Vx
        emu.register_state.sound_timer = 0;
        emu.register_state.gprs[1] = 14;
        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::SoundTimer, Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.sound_timer, 14);
    }

    #[test]
    fn emulate_add() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        // ADD Vx, Vy (no overflow)
        emu.register_state.gprs[0] = 2;
        emu.register_state.gprs[1] = 1;
        emu.register_state.flags = 1;
        assert_eq!(
            emu.emulate_internal(Instruction::Add((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 3);
        assert_eq!(emu.register_state.flags, 0);

        // ADD Vx, byte (with overflow)
        emu.register_state.gprs[0] = 0xff;
        emu.register_state.flags = 0;
        assert_eq!(
            emu.emulate_internal(Instruction::Add((Operand::Gpr(0), Operand::Byte(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0);
        assert_eq!(emu.register_state.flags, 1);

        // ADD I, Vx
        emu.register_state.address_reg = 0x200;
        emu.register_state.gprs[3] = 0x10;
        assert_eq!(
            emu.emulate_internal(Instruction::Add((Operand::AddrReg, Operand::Gpr(3))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.address_reg, 0x210);
        assert_eq!(emu.register_state.flags, 0);
    }

    #[test]
    fn emulate_or() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[0] = 5;
        emu.register_state.gprs[1] = 0x10;

        assert_eq!(
            emu.emulate_internal(Instruction::Or((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0x15);

        emu.register_state.gprs[0] = 0xf0;

        assert_eq!(
            emu.emulate_internal(Instruction::Add((Operand::Gpr(0), Operand::Byte(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0xf1);
    }

    #[test]
    fn emulate_and() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[0] = 0x12;
        emu.register_state.gprs[1] = 0x10;

        assert_eq!(
            emu.emulate_internal(Instruction::And((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0x10);

        emu.register_state.gprs[0] = 0xf0;

        assert_eq!(
            emu.emulate_internal(Instruction::And((Operand::Gpr(0), Operand::Byte(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0);
    }

    #[test]
    fn emulate_xor() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[0] = 0x12;
        emu.register_state.gprs[1] = 0x10;

        assert_eq!(
            emu.emulate_internal(Instruction::Xor((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0x2);

        emu.register_state.gprs[0] = 0xa;

        assert_eq!(
            emu.emulate_internal(Instruction::Xor((Operand::Gpr(0), Operand::Byte(0xa))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0);
    }

    #[test]
    fn emulate_sub() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[0] = 2;
        emu.register_state.gprs[1] = 1;

        assert_eq!(
            emu.emulate_internal(Instruction::Sub((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 1);
        assert_eq!(emu.register_state.flags, 1);

        emu.register_state.gprs[0] = 0;

        assert_eq!(
            emu.emulate_internal(Instruction::Sub((Operand::Gpr(0), Operand::Byte(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0xff);
        assert_eq!(emu.register_state.flags, 0);
    }

    #[test]
    fn emulate_shr() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[0] = 0x12;
        emu.register_state.flags = 1;

        assert_eq!(
            emu.emulate_internal(Instruction::Shr((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 9);
        assert_eq!(emu.register_state.flags, 0);

        emu.register_state.gprs[0] = 0x3;
        emu.register_state.flags = 0;

        assert_eq!(
            emu.emulate_internal(Instruction::Shr((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 1);
        assert_eq!(emu.register_state.flags, 1);
    }

    #[test]
    fn emulate_subn() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[0] = 2;
        emu.register_state.gprs[1] = 1;

        assert_eq!(
            emu.emulate_internal(Instruction::Subn((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0xff);
        assert_eq!(emu.register_state.flags, 0);

        emu.register_state.gprs[0] = 0;

        assert_eq!(
            emu.emulate_internal(Instruction::Subn((Operand::Gpr(0), Operand::Byte(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 1);
        assert_eq!(emu.register_state.flags, 1);
    }

    #[test]
    fn emulate_shl() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[0] = 0x12;
        emu.register_state.flags = 1;

        assert_eq!(
            emu.emulate_internal(Instruction::Shl((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 0x24);
        assert_eq!(emu.register_state.flags, 0);

        emu.register_state.gprs[0] = 0x81;
        emu.register_state.flags = 0;

        assert_eq!(
            emu.emulate_internal(Instruction::Shl((Operand::Gpr(0), Operand::Gpr(1))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[0], 2);
        assert_eq!(emu.register_state.flags, 1);
    }

    // TODO: test RND

    #[derive(Debug, Default)]
    struct MockMemoryWriteExpectation {
        // `None` means that we don't care about the address.
        address: Option<u16>,
        // `None` means that we don't care about the value.
        value: Option<u8>,
        // This is the actual value returned by the function.
        result: Option<()>,
    }

    #[derive(Debug, Default)]
    struct MockMemoryReadExpectation {
        // `None` means that we don't care about the address.
        address: Option<u16>,
        // This is the actual value returned by the function.
        result: Option<u8>,
    }

    #[derive(Debug, Default)]
    struct MockMemory {
        expected_writes: Vec<MockMemoryWriteExpectation>,
        expected_reads: Vec<MockMemoryReadExpectation>,
    }

    impl EmuMemory for MockMemory {
        fn read(&mut self, address: u16) -> Option<u8> {
            // This will panic if we don't expect a read.
            let expectation = self.expected_reads.remove(0);

            if let Some(expected_address) = expectation.address {
                assert_eq!(address, expected_address);
            }

            expectation.result
        }

        fn write(&mut self, address: u16, value: u8) -> Option<()> {
            // This will panic if we don't expect a write.
            let expectation = self.expected_writes.remove(0);

            if let Some(expected_address) = expectation.address {
                assert_eq!(address, expected_address);
            }

            if let Some(expected_value) = expectation.value {
                assert_eq!(value, expected_value);
            }

            expectation.result
        }
    }

    #[test]
    fn store_v0_to_memory() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(address),
            value: Some(value),
            result: Some(()),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;
        emu.register_state.gprs[0] = value;

        assert_eq!(emu.store_gprs_to_memory(Operand::Gpr(0)).unwrap(), ());
        assert_eq!(emu.register_state.address_reg, 0x200);

        assert_eq!(memory.expected_writes.len(), 0);
    }

    #[test]
    fn store_v0_ve_to_memory() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let base_address = 0x300 as u16;

        for i in 0..=0xE {
            memory.expected_writes.push(MockMemoryWriteExpectation {
                address: Some(base_address + i),
                value: Some(i as u8),
                result: Some(()),
            });
        }

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = base_address;
        for i in 0..=0xE {
            emu.register_state.gprs[i] = i as u8;
        }

        assert_eq!(emu.store_gprs_to_memory(Operand::Gpr(0xE)).unwrap(), ());
        assert_eq!(emu.register_state.address_reg, 0x300);

        assert_eq!(memory.expected_writes.len(), 0);
    }

    #[test]
    fn store_v0_vf_to_memory() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let base_address = 0x300 as u16;

        for i in 0..=0xE {
            memory.expected_writes.push(MockMemoryWriteExpectation {
                address: Some(base_address + i),
                value: Some(i as u8),
                result: Some(()),
            });
        }

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(base_address + 0xF),
            value: Some(0xF),
            result: Some(()),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = base_address;
        for i in 0..=0xE {
            emu.register_state.gprs[i] = i as u8;
        }
        emu.register_state.flags = 0xf;

        assert_eq!(emu.store_gprs_to_memory(Operand::Gpr(0xF)).unwrap(), ());
        assert_eq!(emu.register_state.address_reg, 0x300);

        assert_eq!(memory.expected_writes.len(), 0);
    }

    #[test]
    fn store_to_memory_errors() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(address),
            value: Some(value),
            result: Some(()),
        });
        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: None,
            value: None,
            result: None,
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;
        emu.register_state.gprs[0] = value;

        assert_eq!(
            emu.store_gprs_to_memory(Operand::Gpr(1)).unwrap_err(),
            EmulationError::MemoryWriteError(address + 1)
        );
        assert_eq!(emu.register_state.address_reg, 0x200);

        assert_eq!(memory.expected_writes.len(), 0);
    }

    #[test]
    fn load_v0_from_memory() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address),
            result: Some(value),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;

        assert_eq!(emu.load_gprs_from_memory(Operand::Gpr(0)).unwrap(), ());
        assert_eq!(emu.register_state.address_reg, 0x200);
        assert_eq!(emu.register_state.gprs[0], value);

        assert_eq!(memory.expected_reads.len(), 0);
    }

    #[test]
    fn load_v0_ve_from_memory() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let base_address = 0x300 as u16;

        for i in 0..=0xE {
            memory.expected_reads.push(MockMemoryReadExpectation {
                address: Some(base_address + i),
                result: Some(i as u8),
            });
        }

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = base_address;

        assert_eq!(emu.load_gprs_from_memory(Operand::Gpr(0xE)).unwrap(), ());
        assert_eq!(emu.register_state.address_reg, 0x300);
        for i in 0..=0xE {
            assert_eq!(emu.register_state.gprs[i], i as u8);
        }

        assert_eq!(memory.expected_reads.len(), 0);
    }

    #[test]
    fn load_v0_vf_from_memory() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let base_address = 0x300 as u16;

        for i in 0..=0xE {
            memory.expected_reads.push(MockMemoryReadExpectation {
                address: Some(base_address + i),
                result: Some(i as u8),
            });
        }

        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(base_address + 0xF),
            result: Some(0xF),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = base_address;

        assert_eq!(emu.load_gprs_from_memory(Operand::Gpr(0xF)).unwrap(), ());
        assert_eq!(emu.register_state.address_reg, 0x300);
        for i in 0..=0xE {
            assert_eq!(emu.register_state.gprs[i], i as u8);
        }
        assert_eq!(emu.register_state.flags, 0xf);

        assert_eq!(memory.expected_reads.len(), 0);
    }

    #[test]
    fn store_from_memory_errors() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address),
            result: Some(value),
        });
        memory.expected_reads.push(MockMemoryReadExpectation {
            address: None,
            result: None,
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;

        assert_eq!(
            emu.load_gprs_from_memory(Operand::Gpr(1)).unwrap_err(),
            EmulationError::MemoryReadError(address + 1)
        );
        assert_eq!(emu.register_state.address_reg, 0x200);
        assert_eq!(emu.register_state.gprs[0], value);

        assert_eq!(memory.expected_reads.len(), 0);
    }

    #[test]
    fn emulate_ld_i_v0() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(address),
            value: Some(value),
            result: Some(()),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;
        emu.register_state.gprs[0] = value;

        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Memory, Operand::Gpr(0))))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.address_reg, 0x200);

        assert_eq!(memory.expected_writes.len(), 0);
    }

    #[test]
    fn emulate_ld_i_v0_vx_errors() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(address),
            value: Some(value),
            result: Some(()),
        });
        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: None,
            value: None,
            result: None,
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;
        emu.register_state.gprs[0] = value;

        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Memory, Operand::Gpr(1))))
                .unwrap_err(),
            EmulationError::MemoryWriteError(address + 1)
        );
        assert_eq!(emu.register_state.address_reg, 0x200);

        assert_eq!(memory.expected_writes.len(), 0);
    }

    #[test]
    fn emulate_ld_v0_i() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address),
            result: Some(value),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;

        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Gpr(0), Operand::Memory)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.address_reg, 0x200);
        assert_eq!(emu.register_state.gprs[0], value);

        assert_eq!(memory.expected_reads.len(), 0);
    }

    #[test]
    fn emulate_ld_v0_vx_i_errors() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;
        let value = 0x10 as u8;

        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address),
            result: Some(value),
        });
        memory.expected_reads.push(MockMemoryReadExpectation {
            address: None,
            result: None,
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;

        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Gpr(1), Operand::Memory)))
                .unwrap_err(),
            EmulationError::MemoryReadError(address + 1)
        );
        assert_eq!(emu.register_state.address_reg, 0x200);
        assert_eq!(emu.register_state.gprs[0], value);

        assert_eq!(memory.expected_reads.len(), 0);
    }

    #[derive(Debug, Default)]
    struct MockScreenExpectation<T> {
        x: Option<u8>,
        y: Option<u8>,
        result: Option<T>,
    }

    const MOCK_SCREEN_X: usize = 4;
    const MOCK_SCREEN_Y: usize = 5;

    #[derive(Debug)]
    struct MockScreen {
        // `screen[x][y]` is the pixel at `(x, y)`.
        screen: [u8; MOCK_SCREEN_X * MOCK_SCREEN_Y],
        // If `Some`, `get_pixel` calls will fail after this many calls.
        success_get_count: Option<u32>,
        // If `Some`, `set_pixel` calls will fail after this many calls.
        success_set_count: Option<u32>,
    }

    impl MockScreen {
        fn new() -> Self {
            MockScreen {
                screen: [0; MOCK_SCREEN_X * MOCK_SCREEN_Y],
                success_get_count: None,
                success_set_count: None,
            }
        }
    }

    fn handle_wraparound(x: u8, y: u8) -> (usize, usize) {
        (x as usize % MOCK_SCREEN_X, y as usize % MOCK_SCREEN_Y)
    }

    impl EmuScreen for MockScreen {
        fn clear(&mut self) {
            unreachable!();
        }

        fn get_pixel(&mut self, x: u8, y: u8) -> Option<u8> {
            if let Some(mut count) = self.success_get_count {
                count -= 1;
                if count == 0 {
                    return None;
                }
                self.success_get_count = Some(count)
            }

            let (x, y) = handle_wraparound(x, y);
            Some(self.screen[x + y * MOCK_SCREEN_X])
        }

        fn set_pixel(&mut self, x: u8, y: u8, value: u8) -> Option<()> {
            if let Some(mut count) = self.success_set_count {
                count -= 1;
                if count == 0 {
                    return None;
                }
                self.success_set_count = Some(count)
            }

            let (x, y) = handle_wraparound(x, y);
            self.screen[x + y * MOCK_SCREEN_X] = value;
            Some(())
        }
    }

    #[test]
    fn draw_sprite_bytes() {
        let mut screen = MockScreen::new();
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.draw_sprite_byte(0, 0, 0xF0).unwrap();
        emu.draw_sprite_byte(0, 1, 0x90).unwrap();
        emu.draw_sprite_byte(0, 2, 0x90).unwrap();
        emu.draw_sprite_byte(0, 3, 0x90).unwrap();
        emu.draw_sprite_byte(0, 4, 0xF0).unwrap();

        // `VF` should not be modified.
        assert_eq!(emu.register_state.flags, 0);

        // This should end up like:
        // 1111
        // 1001
        // 1001
        // 1001
        // 1111
        let expected = [1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1];

        assert!(
            expected.len() <= screen.screen.len(),
            "Make sure that MOCK_SCREEN_X and MOCK_SCREEN_Y are large enough!"
        );
        for i in 0..expected.len() {
            assert_eq!(expected[i], screen.screen[i]);
        }
    }

    #[test]
    fn draw_sprite_bytes_with_vf() {
        let mut screen = MockScreen::new();
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        // This should give as a conflict.
        screen.screen[1] = 1;

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.draw_sprite_byte(0, 0, 0xF0).unwrap();
        emu.draw_sprite_byte(0, 1, 0x90).unwrap();
        emu.draw_sprite_byte(0, 2, 0x90).unwrap();
        emu.draw_sprite_byte(0, 3, 0x90).unwrap();
        emu.draw_sprite_byte(0, 4, 0xF0).unwrap();

        // `VF` should be set.
        assert_eq!(emu.register_state.flags, 1);

        // This should end up like:
        // 1011
        // 1001
        // 1001
        // 1001
        // 1111
        let expected = [1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1];

        assert!(
            expected.len() <= screen.screen.len(),
            "Make sure that MOCK_SCREEN_X and MOCK_SCREEN_Y are large enough!"
        );
        for i in 0..expected.len() {
            assert_eq!(expected[i], screen.screen[i]);
        }
    }

    #[test]
    fn draw_sprite_bytes_fails_on_get() {
        let mut screen = MockScreen::new();
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        screen.success_get_count = Some(9);

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.draw_sprite_byte(0, 0, 0x1).unwrap();
        assert_eq!(
            emu.draw_sprite_byte(0, 1, 0x90).unwrap_err(),
            EmulationError::ScreenError
        );
    }

    #[test]
    fn draw_sprite_bytes_fails_on_set() {
        let mut screen = MockScreen::new();
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        screen.success_set_count = Some(9);

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.draw_sprite_byte(0, 0, 0x1).unwrap();
        assert_eq!(
            emu.draw_sprite_byte(0, 1, 0x90).unwrap_err(),
            EmulationError::ScreenError
        );
    }

    #[test]
    fn draw_sprite() {
        let mut screen = MockScreen::new();
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;

        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address),
            result: Some(0xF0),
        });
        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address + 1),
            result: Some(0x90),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;

        emu.draw_sprite(0, 0, 2).unwrap();

        // `VF` should not be modified.
        assert_eq!(emu.register_state.flags, 0);

        // This should end up like:
        // 1111
        // 1001
        let expected = [1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

        assert!(
            expected.len() <= screen.screen.len(),
            "Make sure that MOCK_SCREEN_X and MOCK_SCREEN_Y are large enough!"
        );
        for i in 0..expected.len() {
            assert_eq!(expected[i], screen.screen[i]);
        }
    }

    #[test]
    fn emulate_drw() {
        let mut screen = MockScreen::new();
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x200 as u16;

        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address),
            result: Some(0xF0),
        });
        memory.expected_reads.push(MockMemoryReadExpectation {
            address: Some(address + 1),
            result: Some(0x90),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;
        emu.register_state.gprs[0] = 0;
        emu.register_state.gprs[1] = 1;

        assert_eq!(
            emu.emulate_internal(Instruction::Drw((
                Operand::Gpr(0),
                Operand::Gpr(1),
                Operand::Nibble(2)
            )))
            .unwrap(),
            true
        );

        // `VF` should not be modified.
        assert_eq!(emu.register_state.flags, 0);

        // This should end up like:
        // 0000
        // 1111
        // 1001
        // 0000
        // 0000
        let expected = [0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0];

        assert!(
            expected.len() <= screen.screen.len(),
            "Make sure that MOCK_SCREEN_X and MOCK_SCREEN_Y are large enough!"
        );

        for i in 0..expected.len() {
            assert_eq!(expected[i], screen.screen[i]);
        }
    }

    #[derive(Debug)]
    struct MockKeyboard {
        next_keys: Vec<u8>,
    }

    impl Default for MockKeyboard {
        fn default() -> Self {
            MockKeyboard {
                next_keys: Vec::new(),
            }
        }
    }

    impl EmuKeyboard for MockKeyboard {
        fn wait_for_keypress(&mut self) -> EmuKey {
            self.get_key().unwrap()
        }

        fn get_key(&mut self) -> Option<EmuKey> {
            // This will panic if we don't expect a call.
            Some(EmuKey::new(self.next_keys.remove(0)))
        }
    }

    #[test]
    fn emulate_ld_vx_k() {
        let mut screen = TestScreen {};
        let mut keyboard = MockKeyboard::default();
        let mut memory = TestMemory {};

        let key = 5;
        keyboard.next_keys.push(key);

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.gprs[3] = 0;

        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Gpr(3), Operand::Key)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.gprs[3], key);
    }

    #[test]
    fn emulate_ld_f_vx() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = TestMemory {};

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        let index = 5;
        emu.register_state.address_reg = 0x200;
        emu.register_state.gprs[3] = index;

        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Font, Operand::Gpr(3))))
                .unwrap(),
            true
        );
        assert_eq!(
            emu.register_state.address_reg,
            InstructionEmulator::DEFAULT_FONT_BASE_ADDRESS
                + index as u16 * InstructionEmulator::DEFAULT_FONT_SPRITE_SIZE
        );
    }

    #[test]
    fn emulate_ld_b_vx() {
        let mut screen = TestScreen {};
        let mut keyboard = TestKeyboard {};
        let mut memory = MockMemory::default();

        let address = 0x300;

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(address),
            value: Some(1),
            result: Some(()),
        });

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(address + 1),
            value: Some(2),
            result: Some(()),
        });

        memory.expected_writes.push(MockMemoryWriteExpectation {
            address: Some(address + 2),
            value: Some(3),
            result: Some(()),
        });

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.address_reg = address;
        emu.register_state.gprs[3] = 123;

        assert_eq!(
            emu.emulate_internal(Instruction::Ld((Operand::Bcd, Operand::Gpr(3))))
                .unwrap(),
            true
        );

        assert_eq!(memory.expected_writes.len(), 0);
    }

    #[test]
    fn emulate_skp() {
        let mut screen = TestScreen {};
        let mut keyboard = MockKeyboard::default();
        let mut memory = TestMemory {};

        let skip = 5;
        let not_skip = 7;
        keyboard.next_keys.push(skip);
        keyboard.next_keys.push(not_skip);

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.pc = 0x250;
        emu.register_state.gprs[6] = skip;

        assert_eq!(
            emu.emulate_internal(Instruction::Skp(Operand::Gpr(6)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x252);

        emu.register_state.pc = 0x350;
        emu.register_state.gprs[6] = skip;

        assert_eq!(
            emu.emulate_internal(Instruction::Skp(Operand::Gpr(6)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x350);
    }

    #[test]
    fn emulate_sknp() {
        let mut screen = TestScreen {};
        let mut keyboard = MockKeyboard::default();
        let mut memory = TestMemory {};

        keyboard.next_keys.push(5);
        keyboard.next_keys.push(7);

        let mut emu = InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        emu.register_state.pc = 0x250;
        emu.register_state.gprs[6] = 5;

        assert_eq!(
            emu.emulate_internal(Instruction::Sknp(Operand::Gpr(6)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x250);

        emu.register_state.pc = 0x350;
        emu.register_state.gprs[6] = 5;

        assert_eq!(
            emu.emulate_internal(Instruction::Sknp(Operand::Gpr(6)))
                .unwrap(),
            true
        );
        assert_eq!(emu.register_state.pc, 0x352);
    }
}
