//! A CHIP8 instruction emulator.

use decoder::{decode, Instruction, Operand};
use std::error::Error;
use std::fmt;

/// Abstracts access to the display.
pub trait Screen {
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
    fn get_pixel(&self, x: u8, y: u8) -> Option<u8>;

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

/// Abstracts access to the keyboard.
pub trait Keyboard {
    /// Waits until a key is pressend and returns the code of the key.
    fn wait_for_keypress(&self) -> u8;
}

/// Abstracts access to memory.
pub trait Memory {
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
    fn read(&self, address: u16) -> Option<u8>;

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
#[derive(Debug, Default)]
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
    screen: &'a mut dyn Screen,

    /// Used to get key press events.
    keyboard: &'a mut dyn Keyboard,

    /// Used to access the memory.
    memory: &'a mut dyn Memory,
}

impl<'a> InstructionEmulator<'a> {
    /// Creates a new `InstructionEmulator`.
    ///
    /// The initial registers are all 0.
    ///
    /// # Arguments
    ///
    /// * `screen` - A structure that implements the `Screen` trait. Used to draw to the screen.
    /// * `keyboard` - A structure that implements the `Keyboard` trait. Used to get key press events.
    /// * `memory` - A structure that implements the `Memory` trait. Used to access memory.
    pub fn new(
        screen: &'a mut dyn Screen,
        keyboard: &'a mut dyn Keyboard,
        memory: &'a mut dyn Memory,
    ) -> Self {
        InstructionEmulator::with_initial_state(Default::default(), screen, keyboard, memory)
    }

    /// Creates a new `InstructionEmulator` with a given `RegisterState`.
    ///
    /// # Arguments
    ///
    /// * `register_state` - The initial `RegisterState` to be used.
    /// * `screen` - A structure that implements the `Screen` trait. Used to draw to the screen.
    /// * `keyboard` - A structure that implements the `Keyboard` trait. Used to get key press events.
    /// * `memory` - A structure that implements the `Memory` trait. Used to access memory.
    pub fn with_initial_state(
        register_state: RegisterState,
        screen: &'a mut dyn Screen,
        keyboard: &'a mut dyn Keyboard,
        memory: &'a mut dyn Memory,
    ) -> Self {
        InstructionEmulator {
            register_state,
            stack: Default::default(),
            screen,
            keyboard,
            memory,
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
            Some(ins) => self.emulate_instruction(ins),
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
            Instruction::Sys(_) => Err(EmulationError::InstructionNotSupported(instruction)),
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
                // Save the current program counter on the stack.
                self.push_stack(self.register_state.pc)?;

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
                // Set the first operand to the value of the second operand.
                self.set_operand_value(&op1, self.get_operand_value(&op2))?;

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
                let _x = self.get_operand_value(&op1);
                let _y = self.get_operand_value(&op2);
                let _n = self.get_operand_value(&op3);

                unreachable!();
            }
            Instruction::Skp(op) => {
                // Get the expected key value.
                let expected_key = self.get_operand_value(&op) as u8;

                // Wait for a key to be pressed.
                let key = self.keyboard.wait_for_keypress();

                if expected_key == key {
                    // Skip the next instruction.
                    self.register_state.pc += 2;
                }

                // Update PC.
                // This is OK because in the skipped case we only increment PC by 2.
                Ok(true)
            }
            Instruction::Sknp(op) => {
                // Get the expected key value.
                let expected_key = self.get_operand_value(&op) as u8;

                // Wait for a key to be pressed.
                let key = self.keyboard.wait_for_keypress();

                if expected_key != key {
                    // Skip the next instruction.
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
    /// If `value` does not fit inside the given operand the function returns `EmulationError::SetOperandValueOverflow`.    ///
    /// For operands that do not support this operation the function returns. `EmulationError::InvalidSetOperandRequest`.
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
        unreachable!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestScreen;
    struct TestKeyboard;
    struct TestMemory;

    impl Screen for TestScreen {
        fn clear(&mut self) {}
        fn get_pixel(&self, _x: u8, _y: u8) -> Option<u8> {
            Some(0)
        }
        fn set_pixel(&mut self, _x: u8, _y: u8, _pixel: u8) -> Option<()> {
            Some(())
        }
    }

    impl Keyboard for TestKeyboard {
        fn wait_for_keypress(&self) -> u8 {
            0
        }
    }

    impl Memory for TestMemory {
        fn read(&self, _address: u16) -> Option<u8> {
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

        assert_eq!(
            emu.emulate_internal(Instruction::Sys(Operand::Address(0)))
                .unwrap_err(),
            EmulationError::InstructionNotSupported(Instruction::Sys(Operand::Address(0)))
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
        assert_eq!(emu.stack[0], 0x100);
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

        // TODO: Test LD Vx, K
        // TODO: Test LD F, Vx
        // TODO: Test LD B, Vx
        // TODO: Test LD [I], Vx
        // TODO: Test LD Vx, [I]
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

        // TODO: Test all the other ADD variants.
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
    // TODO: test DRW
    // TODO: test SKP
    // TODO: test SKNP
}
