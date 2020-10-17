use std::error::Error;
use std::fmt;

/// CHIP8 programs can access up to 4KB of memory.
pub const DEFAULT_MEMORY_SIZE: usize = 4096;

/// By default, programs are loaded at address 0x200.
pub const DEFAULT_PROGRAM_BASE: usize = 0x200;

/// By default, the interpreter memory area starts at address 0.
pub const DEFAULT_INTERPRETER_ZONE_BASE: usize = 0;

/// Describes the CHIP8 memory as used by `instruction_emulator`.
pub struct Memory {
    /// Holds the memory contents. `memory[0]` corresponds to address `0`.
    memory: Vec<u8>,
}

impl Default for Memory {
    fn default() -> Self {
        Self {
            // Use the default memory size.
            memory: vec![0; DEFAULT_MEMORY_SIZE],
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum EmuMemoryError {
    LoadBaseNotInMemory((usize, usize)),
    PayloadDoesNotFitInMemory((usize, usize)),
}

impl fmt::Display for EmuMemoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EmuMemoryError::LoadBaseNotInMemory((base, size)) => write!(
                f,
                "Loading base {:x} is outside the available memory (size {:x})",
                base, size
            ),
            EmuMemoryError::PayloadDoesNotFitInMemory((available_space, payload_size)) => write!(
                f,
                "Payload with size {:x} does not fit in the available {:x} bytes of memory",
                payload_size, available_space
            ),
        }
    }
}

impl Error for EmuMemoryError {}

impl Memory {
    pub fn load_program(&mut self, program: &Vec<u8>) -> Result<(), EmuMemoryError> {
        self.load_at(program, DEFAULT_PROGRAM_BASE)
    }

    pub fn load_fonts(&mut self, sprites: &Vec<u8>) -> Result<(), EmuMemoryError> {
        self.load_at(sprites, DEFAULT_INTERPRETER_ZONE_BASE)
    }

    fn load_at(&mut self, payload: &Vec<u8>, address: usize) -> Result<(), EmuMemoryError> {
        if address >= self.memory.capacity() {
            Err(EmuMemoryError::LoadBaseNotInMemory((
                address,
                self.memory.capacity(),
            )))
        } else {
            let available_space = self.memory.capacity() - address;
            if available_space < payload.len() {
                Err(EmuMemoryError::PayloadDoesNotFitInMemory((
                    available_space,
                    payload.len(),
                )))
            } else {
                // TODO: there has to be a better way of doing this.
                for (pos, e) in payload.iter().enumerate() {
                    self.memory[address + pos] = *e;
                }
                Ok(())
            }
        }
    }
}

impl instruction_emulator::EmuMemory for Memory {
    fn read(&mut self, address: u16) -> Option<u8> {
        let address = address as usize;
        if address >= self.memory.len() {
            None
        } else {
            Some(self.memory[address])
        }
    }

    fn write(&mut self, address: u16, value: u8) -> Option<()> {
        let address = address as usize;
        if address >= self.memory.capacity() {
            None
        } else {
            self.memory[address] = value;
            Some(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load_program() {
        let mut memory = Memory::default();

        let program: Vec<u8> = vec![0, 1, 2, 3];

        memory.load_program(&program).unwrap();

        for i in 0..program.len() {
            assert_eq!(memory.memory[DEFAULT_PROGRAM_BASE + i], program[i])
        }
    }

    #[test]
    fn load_fonts() {
        let mut memory = Memory::default();

        let fonts: Vec<u8> = vec![0, 1, 2, 3];

        memory.load_fonts(&fonts).unwrap();

        for i in 0..fonts.len() {
            assert_eq!(memory.memory[DEFAULT_INTERPRETER_ZONE_BASE + i], fonts[i])
        }
    }

    #[test]
    fn load_base_error() {
        let memory_size = 0x100;
        let mut memory = Memory {
            memory: vec![0; memory_size],
        };

        let program: Vec<u8> = vec![0, 1, 2, 3];

        assert_eq!(
            memory.load_program(&program).unwrap_err(),
            EmuMemoryError::LoadBaseNotInMemory((DEFAULT_PROGRAM_BASE, memory_size))
        );
    }

    #[test]
    fn load_pyload_size_error() {
        let memory_size = 0x2;
        let mut memory = Memory {
            memory: vec![0; memory_size],
        };

        let program: Vec<u8> = vec![0, 1, 2, 3];

        assert_eq!(
            memory.load_at(&program, 0).unwrap_err(),
            EmuMemoryError::PayloadDoesNotFitInMemory((memory_size, program.len()))
        );
    }
}
