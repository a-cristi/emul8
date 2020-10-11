//! A CHIP8 instruction decoder.

use std::fmt;

/// An Operand of a CHIP8 instruction.
#[derive(Debug, PartialEq)]
pub enum Operand {
    /// The operand is a 12-bit address. The inner `u16` holds this address. It will never be higher than `0xFFF`.
    Address(u16),
    /// A general purpose register.
    /// CHIP8 has 16 general purpose registers (V0 through VF).
    /// Note that VF is not included here as it is used as a flags registers. See `Flags`.
    Gpr(u8),
    /// The VF register, used as a flags register.
    Flags,
    /// An 8-bit value. The inner `u8` holds this value.
    Byte(u8),
    /// An 4-bit value. The inner `u8` holds this value. It will never be higher than `0xF`.
    Nibble(u8),
    /// The special 16-bit `I` register used to hold addresses.
    AddrReg,
    /// The instruction accesses a memory range.
    Memory,
    /// Delay timer register.
    DelayTimer,
    /// Sound timer register.
    SoundTimer,
    /// A key that was pressed.
    Key,
    /// The instruction loads a hexadecimal font.
    Font,
    /// The instruction operated on a BCD representation.
    Bcd,
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operand::Address(addr) => write!(f, "[{:#05x}]", addr),
            Operand::Gpr(index) => write!(f, "V{:x}", index),
            Operand::Flags => write!(f, "Vf"),
            Operand::Byte(value) => write!(f, "{:#04x}", value),
            Operand::Nibble(value) => write!(f, "{:#x}", value),
            Operand::AddrReg => write!(f, "I"),
            Operand::Memory => write!(f, "[I]"),
            Operand::DelayTimer => write!(f, "DT"),
            Operand::SoundTimer => write!(f, "ST"),
            Operand::Key => write!(f, "K"),
            Operand::Font => write!(f, "F"),
            Operand::Bcd => write!(f, "B"),
        }
    }
}

/// Represents a decoded CHIP8 instruction. See http://devernay.free.fr/hacks/chip8/C8TECH10.HTM for details.
#[derive(Debug, PartialEq)]
pub enum Instruction {
    /// `SYS addr` - Jumps at the address `addr`. Most modern interpreters ignore it.
    Sys(Operand),
    /// `CLS` - Clears the display.
    Cls,
    /// `RET` - Return from subroutine.
    Ret,
    /// `JP addr/V0, addr` - Jumps at `addr` or `addr + V0`.
    /// The operand is always `Operand::Address`. The form that uses `V0` has it as an implicit operand.
    Jp((Operand, Option<Operand>)),
    /// `CALL addr` - Calls the subroutine at `addr`.
    Call(Operand),
    /// `SE Vx, byte/Vx, Vy` - Skips the next instruction if the first operand is equal to the second operand.
    Se((Operand, Operand)),
    /// `SNE Vx, byte/Vx, Vy` - Skips the next instruction if the first operand is not equal to the second operand.
    Sne((Operand, Operand)),
    /// `LD Vx, byte/Vx, Vy/I, addr/Vx, DT/Vx, K/DT, Vx/ST, Vx/F, Vx/B, Vx/[I], Vx/Vx, [I]` - Loads the first operand with the value of the second operand.
    /// The form `LD Vx, K` waits until a key is pressed.
    Ld((Operand, Operand)),
    /// `ADD Vx, byte/Vx, Vy/I, Vx` - Adds the first and the second operand and sets the first operand to the result.
    Add((Operand, Operand)),
    /// `OR Vx, Vy` - Performs a logical `or` of the first and the second operand and sets the first operand to the result.
    Or((Operand, Operand)),
    /// `AND Vx, Vy` - Performs a logical `and` of the first and the second operand and sets the first operand to the result.
    /// If the result does not fit the 8-bit register (it is larger than 255), only the lower 8 bits are kept and `Vf` is set to 1.
    And((Operand, Operand)),
    /// `OR Vx, Vy` - Performs a logical `xor` of the first and the second operand and sets the first operand to the result.
    Xor((Operand, Operand)),
    /// `SUB Vx, Vy` - Subtracts the second operand from the first operand and sets the first operand to the result.
    Sub((Operand, Operand)),
    /// `SHR Vx {, Vy}` - Shifts the first operand to the right with 1 and stores the result in the first operand.
    /// `Vf` is set to 1 if the previous value of `Vx` had the most significant bit set to 1.
    Shr((Operand, Operand)),
    /// `SUBN Vx, Vy` - Subtracts the second operand from the first operand and sets the first operand to the result.
    Subn((Operand, Operand)),
    /// `SHL Vx {, Vy}` - Shifts the first operand to the left with 1 and stores the result in the first operand.
    Shl((Operand, Operand)),
    /// `RND Vx, byte` - Sets `Vx` to the result of a logical `and` between `byte` and a randomly generated value in the range `[0, 255]`.
    Rnd((Operand, Operand)),
    /// `DRW Vx, Vy, nibble` - Displays `nibble`-byte sprites starting at the memory address currently stored in `I` at coordinates `(Vx, Vy)`.
    /// Sprites are `xor`ed onto the screen. If any pixels are erased `Vf` is set to 1.
    Drw((Operand, Operand, Operand)),
    /// `SKP Vx` - Skips the next instruction if a key equal to the value of `Vx` is pressed.
    Skp(Operand),
    /// `SKP Vx` - Skips the next instruction if a key not equal to the value of `Vx` is pressed.
    Sknp(Operand),
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Instruction::Sys(o) => write!(f, "SYS {}", o),
            Instruction::Cls => write!(f, "CLS"),
            Instruction::Ret => write!(f, "RET"),
            Instruction::Jp((o1, o2)) => match o2 {
                Some(o) => write!(f, "JP {}, {}", o1, o),
                None => write!(f, "JP {}", o1),
            },
            Instruction::Call(o) => write!(f, "CALL {}", o),
            Instruction::Se((o1, o2)) => write!(f, "SE {}, {}", o1, o2),
            Instruction::Sne((o1, o2)) => write!(f, "SNE {}, {}", o1, o2),
            Instruction::Ld((o1, o2)) => write!(f, "LD {}, {}", o1, o2),
            Instruction::Add((o1, o2)) => write!(f, "ADD {}, {}", o1, o2),
            Instruction::Or((o1, o2)) => write!(f, "OR {}, {}", o1, o2),
            Instruction::And((o1, o2)) => write!(f, "AND {}, {}", o1, o2),
            Instruction::Xor((o1, o2)) => write!(f, "XOR {}, {}", o1, o2),
            Instruction::Sub((o1, o2)) => write!(f, "SUB {}, {}", o1, o2),
            Instruction::Shr((o1, o2)) => write!(f, "Shr {}, {}", o1, o2),
            Instruction::Subn((o1, o2)) => write!(f, "SUBN {}, {}", o1, o2),
            Instruction::Shl((o1, o2)) => write!(f, "SHL {}, {}", o1, o2),
            Instruction::Rnd((o1, o2)) => write!(f, "RND {}, {}", o1, o2),
            Instruction::Drw((o1, o2, o3)) => write!(f, "DRW {}, {}, {}", o1, o2, o3),
            Instruction::Skp(o) => write!(f, "SKP {}", o),
            Instruction::Sknp(o) => write!(f, "SKNP {}", o),
        }
    }
}

/// Decodes an instruction.
///
/// On success, returns `Some(Instruction)` that describes the deocded instruction and its operands.
/// If the instruction is not valid, returns `None`.
///
/// # Arguments
///
/// * `code` - A `u8` slice that contains the instruction to be decoded. CHIP8 instructions are always 2 bytes long.
///
/// # Examples
///
/// ```rust
/// # use decoder::*;
/// # fn main() {
///     let code: [u8; 2] = [0x81, 0x20];
///     let ins = decoder::decode(&code).unwrap();
///     assert_eq!(ins, Instruction::Ld((Operand::Gpr(1), Operand::Gpr(2))));
/// # }
/// ```
pub fn decode(code: &[u8; 2]) -> Option<Instruction> {
    // First, look for `CLS` and `RET`.
    if code[0] == 0 {
        if code[1] == 0xE0 {
            // 00E0
            return Some(Instruction::Cls);
        } else if code[1] == 0xEE {
            // 00EE
            return Some(Instruction::Ret);
        }
    }

    // Now handle all the other instructions.
    let ins = (code[0] & 0xF0) >> 4;

    match ins {
        0x0 => Some(Instruction::Sys(make_address(code))), // 0nnn
        0x1 => Some(Instruction::Jp((make_address(code), None))), // 1nnn
        0x2 => Some(Instruction::Call(make_address(code))), // 2nnn
        0x3 => Some(Instruction::Se((
            make_gpr(code[0] & 0xF),
            make_byte(code[1]),
        ))), // 3xkk
        0x4 => Some(Instruction::Sne((
            make_gpr(code[0] & 0xF),
            make_byte(code[1]),
        ))), // 3xkk
        0x5 => match code[1] & 0xF {
            // 5xy0
            0 => Some(Instruction::Se((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            _ => None,
        },
        0x6 => Some(Instruction::Ld((
            make_gpr(code[0] & 0xF),
            make_byte(code[1]),
        ))), // 6xkk
        0x7 => Some(Instruction::Add((
            make_gpr(code[0] & 0xF),
            make_byte(code[1]),
        ))), // 7xkk
        0x8 => match code[1] & 0xF {
            // 8xy0
            0x0 => Some(Instruction::Ld((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xy1
            0x1 => Some(Instruction::Or((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xy2
            0x2 => Some(Instruction::And((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xy3
            0x3 => Some(Instruction::Xor((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xy4
            0x4 => Some(Instruction::Add((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xy5
            0x5 => Some(Instruction::Sub((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xy6
            0x6 => Some(Instruction::Shr((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xy7
            0x7 => Some(Instruction::Subn((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            // 8xyE
            0xE => Some(Instruction::Shl((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            _ => None,
        },
        0x9 => match code[1] & 0xF {
            // 9xy0
            0x0 => Some(Instruction::Sne((
                make_gpr(code[0] & 0xF),
                make_gpr((code[1] & 0xF0) >> 4),
            ))),
            _ => None,
        },
        0xA => Some(Instruction::Ld((Operand::AddrReg, make_address(code)))), // Annn
        0xB => Some(Instruction::Jp((make_gpr(0), Some(make_address(code))))), // Bnnn
        0xC => Some(Instruction::Rnd((
            make_gpr(code[0] & 0xF),
            make_byte(code[1]),
        ))), // Cxkk
        // Dxyn
        0xD => Some(Instruction::Drw((
            make_gpr(code[0] & 0xF),
            make_gpr((code[1] & 0xF0) >> 4),
            make_nibble(code[1] & 0xF),
        ))),
        0xE => match code[1] {
            // Ex9E
            0x9E => Some(Instruction::Skp(make_gpr(code[0] & 0xF))),
            // ExA1
            0xA1 => Some(Instruction::Sknp(make_gpr(code[0] & 0xF))),
            _ => None,
        },
        0xF => match code[1] {
            // Fx07
            0x07 => Some(Instruction::Ld((
                make_gpr(code[0] & 0xF),
                Operand::DelayTimer,
            ))),
            // Fx0A
            0x0A => Some(Instruction::Ld((make_gpr(code[0] & 0xF), Operand::Key))),
            // Fx15
            0x15 => Some(Instruction::Ld((
                Operand::DelayTimer,
                make_gpr(code[0] & 0xF),
            ))),
            // Fx18
            0x18 => Some(Instruction::Ld((
                Operand::SoundTimer,
                make_gpr(code[0] & 0xF),
            ))),
            // Fx1E
            0x1E => Some(Instruction::Add((
                Operand::AddrReg,
                make_gpr(code[0] & 0xF),
            ))),
            // Fx29
            0x29 => Some(Instruction::Ld((Operand::Font, make_gpr(code[0] & 0xF)))),
            // Fx33
            0x33 => Some(Instruction::Ld((Operand::Bcd, make_gpr(code[0] & 0xF)))),
            // Fx55
            0x55 => Some(Instruction::Ld((Operand::Memory, make_gpr(code[0] & 0xF)))),
            // Fx65
            0x65 => Some(Instruction::Ld((make_gpr(code[0] & 0xF), Operand::Memory))),
            _ => None,
        },
        _ => unreachable!(),
    }
}

/// Returns an `Operand::Address` that wraps a `u8` value.
///
/// # Arguments
///
/// * `code` - The instruction from which the 12-bits address will be extracted.
fn make_address(code: &[u8; 2]) -> Operand {
    Operand::Address(((code[0] as u16 & 0xF) << 8) | code[1] as u16)
}

/// Returns a general purpose register or a flags operand.
///
/// # Arguments
///
/// * `index` - The register index.
///
/// # Returns
///
/// * If `index` is less than 15, returns a `Operand::Gpr` variant that wraps the `index`.
/// * Else, returns `Operand::Flags`.
fn make_gpr(index: u8) -> Operand {
    if index < 0xF {
        Operand::Gpr(index)
    } else {
        Operand::Flags
    }
}

/// Returns an `Operand::Byte` that wraps a `u8` value.
///
/// # Arguments
///
/// * `value` - The value of the byte.
fn make_byte(value: u8) -> Operand {
    Operand::Byte(value)
}

/// Returns an `Operand::Nibble` that wraps a `u8` value.
///
/// # Arguments
///
/// * `value` - The value of the byte.
///
/// # Errors
///
/// If `value` does not fit in 4-bytes (it is higher than 15), the function panics.
fn make_nibble(value: u8) -> Operand {
    assert!(value <= 0xF, "Nibble value can not be hifger than 0xF!");
    Operand::Nibble(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn format_instruction() {
        assert_eq!(
            format!("{}", Instruction::Sys(Operand::Address(0xFFF))),
            "SYS [0xfff]"
        );
        assert_eq!(
            format!("{}", Instruction::Sys(Operand::Address(0x123))),
            "SYS [0x123]"
        );
        assert_eq!(
            format!("{}", Instruction::Jp((Operand::Address(0xFFF), None))),
            "JP [0xfff]"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Jp((Operand::Gpr(0), Some(Operand::Address(0x123))))
            ),
            "JP V0, [0x123]"
        );
        assert_eq!(
            format!("{}", Instruction::Call(Operand::Address(0xFFF))),
            "CALL [0xfff]"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Se((Operand::Gpr(1), Operand::Byte(0x12)))
            ),
            "SE V1, 0x12"
        );
        assert_eq!(
            format!("{}", Instruction::Se((Operand::Flags, Operand::Byte(0x12)))),
            "SE Vf, 0x12"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Sne((Operand::Gpr(1), Operand::Byte(0x12)))
            ),
            "SNE V1, 0x12"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Sne((Operand::Flags, Operand::Byte(0x12)))
            ),
            "SNE Vf, 0x12"
        );
        assert_eq!(
            format!("{}", Instruction::Se((Operand::Gpr(1), Operand::Gpr(2)))),
            "SE V1, V2"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Ld((Operand::Gpr(1), Operand::Byte(0x12)))
            ),
            "LD V1, 0x12"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Add((Operand::Gpr(1), Operand::Byte(0x12)))
            ),
            "ADD V1, 0x12"
        );
        assert_eq!(
            format!("{}", Instruction::Ld((Operand::Gpr(1), Operand::Gpr(2)))),
            "LD V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::Or((Operand::Gpr(1), Operand::Gpr(2)))),
            "OR V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::And((Operand::Gpr(1), Operand::Gpr(2)))),
            "AND V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::Xor((Operand::Gpr(1), Operand::Gpr(2)))),
            "XOR V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::Add((Operand::Gpr(1), Operand::Gpr(2)))),
            "ADD V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::Shr((Operand::Gpr(1), Operand::Gpr(2)))),
            "Shr V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::Subn((Operand::Gpr(1), Operand::Gpr(2)))),
            "SUBN V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::Shl((Operand::Gpr(1), Operand::Gpr(2)))),
            "SHL V1, V2"
        );
        assert_eq!(
            format!("{}", Instruction::Sne((Operand::Gpr(1), Operand::Gpr(2)))),
            "SNE V1, V2"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Ld((Operand::AddrReg, Operand::Address(0xEEE)))
            ),
            "LD I, [0xeee]"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Ld((Operand::Gpr(0), Operand::Address(0xEDD)))
            ),
            "LD V0, [0xedd]"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Rnd((Operand::Gpr(0xA), Operand::Byte(0x53)))
            ),
            "RND Va, 0x53"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Drw((Operand::Gpr(0xA), Operand::Gpr(0xB), Operand::Nibble(0x3)))
            ),
            "DRW Va, Vb, 0x3"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Ld((Operand::Gpr(0x8), Operand::DelayTimer))
            ),
            "LD V8, DT"
        );
        assert_eq!(
            format!("{}", Instruction::Ld((Operand::Gpr(0x8), Operand::Key))),
            "LD V8, K"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Ld((Operand::DelayTimer, Operand::Gpr(0x8)))
            ),
            "LD DT, V8"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Ld((Operand::SoundTimer, Operand::Gpr(0x8)))
            ),
            "LD ST, V8"
        );
        assert_eq!(
            format!(
                "{}",
                Instruction::Add((Operand::AddrReg, Operand::Gpr(0x8)))
            ),
            "ADD I, V8"
        );
        assert_eq!(
            format!("{}", Instruction::Ld((Operand::Font, Operand::Gpr(0x8)))),
            "LD F, V8"
        );
        assert_eq!(
            format!("{}", Instruction::Ld((Operand::Bcd, Operand::Gpr(0x8)))),
            "LD B, V8"
        );
        assert_eq!(
            format!("{}", Instruction::Ld((Operand::Memory, Operand::Gpr(0x8)))),
            "LD [I], V8"
        );
        assert_eq!(
            format!("{}", Instruction::Ld((Operand::Gpr(0x8), Operand::Memory))),
            "LD V8, [I]"
        );
    }

    #[test]
    fn format_operand() {
        assert_eq!(format!("{}", Operand::Address(0xF23)), "[0xf23]");
        assert_eq!(format!("{}", Operand::Address(0xAB)), "[0x0ab]");
        assert_eq!(format!("{}", Operand::Address(0x1)), "[0x001]");

        assert_eq!(format!("{}", Operand::Gpr(0)), "V0");
        assert_eq!(format!("{}", Operand::Gpr(0xE)), "Ve");

        assert_eq!(format!("{}", Operand::Flags), "Vf");

        assert_eq!(format!("{}", Operand::Byte(0x2)), "0x02");
        assert_eq!(format!("{}", Operand::Byte(0xFF)), "0xff");

        assert_eq!(format!("{}", Operand::Nibble(7)), "0x7");

        assert_eq!(format!("{}", Operand::AddrReg), "I");

        assert_eq!(format!("{}", Operand::Memory), "[I]");

        assert_eq!(format!("{}", Operand::DelayTimer), "DT");

        assert_eq!(format!("{}", Operand::SoundTimer), "ST");

        assert_eq!(format!("{}", Operand::Key), "K");

        assert_eq!(format!("{}", Operand::Font), "F");

        assert_eq!(format!("{}", Operand::Bcd), "B");
    }

    #[test]
    fn decoder() {
        let code: [u8; 2] = [0x0F, 0xFF];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Sys(Operand::Address(0xFFF))
        );

        let code: [u8; 2] = [0x01, 0x23];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Sys(Operand::Address(0x123))
        );

        let code: [u8; 2] = [0x00, 0xE0];
        assert_eq!(decode(&code).unwrap(), Instruction::Cls);

        let code: [u8; 2] = [0x00, 0xEE];
        assert_eq!(decode(&code).unwrap(), Instruction::Ret);

        let code: [u8; 2] = [0x1F, 0xFF];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Jp((Operand::Address(0xFFF), None))
        );

        let code: [u8; 2] = [0xB1, 0x23];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Jp((Operand::Gpr(0), Some(Operand::Address(0x123))))
        );

        let code: [u8; 2] = [0x2F, 0xFF];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Call(Operand::Address(0xFFF))
        );

        let code: [u8; 2] = [0x31, 0x12];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Se((Operand::Gpr(1), Operand::Byte(0x12)))
        );

        let code: [u8; 2] = [0x3F, 0x12];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Se((Operand::Flags, Operand::Byte(0x12)))
        );

        let code: [u8; 2] = [0x41, 0x12];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Sne((Operand::Gpr(1), Operand::Byte(0x12)))
        );

        let code: [u8; 2] = [0x4F, 0x12];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Sne((Operand::Flags, Operand::Byte(0x12)))
        );

        let code: [u8; 2] = [0x51, 0x20];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Se((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x51, 0x21];
        assert_eq!(decode(&code), None);

        let code: [u8; 2] = [0x61, 0x12];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Gpr(1), Operand::Byte(0x12)))
        );

        let code: [u8; 2] = [0x71, 0x12];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Add((Operand::Gpr(1), Operand::Byte(0x12)))
        );

        let code: [u8; 2] = [0x81, 0x20];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x81, 0x21];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Or((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x81, 0x22];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::And((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x81, 0x23];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Xor((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x81, 0x24];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Add((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x81, 0x26];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Shr((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x81, 0x27];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Subn((Operand::Gpr(1), Operand::Gpr(2)))
        );

        let code: [u8; 2] = [0x81, 0x2E];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Shl((Operand::Gpr(1), Operand::Gpr(2)))
        );

        for i in 8..0xE {
            let code: [u8; 2] = [0x81, 0x20 | (i as u8)];
            assert_eq!(decode(&code), None);
        }

        let code: [u8; 2] = [0x81, 0x2F];
        assert_eq!(decode(&code), None);

        let code: [u8; 2] = [0x91, 0x20];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Sne((Operand::Gpr(1), Operand::Gpr(2)))
        );

        for i in 8..=0xF {
            let code: [u8; 2] = [0x91, 0x20 | (i as u8)];
            assert_eq!(decode(&code), None);
        }

        let code: [u8; 2] = [0xAE, 0xEE];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::AddrReg, Operand::Address(0xEEE)))
        );

        let code: [u8; 2] = [0xCA, 0x53];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Rnd((Operand::Gpr(0xA), Operand::Byte(0x53)))
        );

        let code: [u8; 2] = [0xDA, 0xB3];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Drw((Operand::Gpr(0xA), Operand::Gpr(0xB), Operand::Nibble(0x3)))
        );

        let code: [u8; 2] = [0xEC, 0x9E];
        assert_eq!(decode(&code).unwrap(), Instruction::Skp(Operand::Gpr(0xC)));

        let code: [u8; 2] = [0xEC, 0xA1];
        assert_eq!(decode(&code).unwrap(), Instruction::Sknp(Operand::Gpr(0xC)));

        let code: [u8; 2] = [0xEC, 0xF0];
        assert_eq!(decode(&code), None);

        let code: [u8; 2] = [0xF8, 0x07];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Gpr(0x8), Operand::DelayTimer))
        );

        let code: [u8; 2] = [0xF8, 0x0A];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Gpr(0x8), Operand::Key))
        );

        let code: [u8; 2] = [0xF8, 0x15];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::DelayTimer, Operand::Gpr(0x8)))
        );

        let code: [u8; 2] = [0xF8, 0x18];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::SoundTimer, Operand::Gpr(0x8)))
        );

        let code: [u8; 2] = [0xF8, 0x1E];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Add((Operand::AddrReg, Operand::Gpr(0x8)))
        );

        let code: [u8; 2] = [0xF8, 0x29];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Font, Operand::Gpr(0x8)))
        );

        let code: [u8; 2] = [0xF8, 0x33];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Bcd, Operand::Gpr(0x8)))
        );

        let code: [u8; 2] = [0xF8, 0x55];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Memory, Operand::Gpr(0x8)))
        );

        let code: [u8; 2] = [0xF8, 0x65];
        assert_eq!(
            decode(&code).unwrap(),
            Instruction::Ld((Operand::Gpr(0x8), Operand::Memory))
        );
    }
}
