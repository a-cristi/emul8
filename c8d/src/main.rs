use clap::{App, Arg};
use decoder;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::num::ParseIntError;
use std::path::Path;

fn get_code_from_file(path: &Path) -> std::io::Result<Vec<u8>> {
    let mut file = File::open(path)?;

    let mut contents = Vec::new();
    file.read_to_end(&mut contents)?;

    Ok(contents)
}

fn get_code_from_str(s: &str) -> Result<Vec<u8>, ParseIntError> {
    let mut v = Vec::new();

    let mut chrs = s.chars();

    for _ in (1..s.len()).step_by(2) {
        let high = chrs.next().unwrap();
        let low = chrs.next().unwrap();

        let high = u8::from_str_radix(&high.to_string(), 16)?;
        let low = u8::from_str_radix(&low.to_string(), 16)?;

        v.push((high << 4) | low);
    }

    Ok(v)
}

#[derive(Debug)]
struct AppError {
    why: String,
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.why)
    }
}

impl Error for AppError {}

fn main() -> Result<(), Box<dyn Error>> {
    let matches = App::new("c8d")
        .version("0.1")
        .author("Cristi")
        .about("CHIP8 disassembler")
        .arg(
            Arg::with_name("input")
                .short("-f")
                .long("file")
                .value_name("FILE")
                .help("The file to disassemble")
                .takes_value(true)
                .required(true)
                .conflicts_with("code"),
        )
        .arg(
            Arg::with_name("code")
                .short("-x")
                .long("hex")
                .value_name("HEX STRING")
                .help("Hexstring to disassemble")
                .takes_value(true)
                .required(true)
                .conflicts_with("input"),
        )
        .get_matches();

    let code: Vec<u8>;

    if let Some(path) = matches.value_of("input") {
        code = get_code_from_file(Path::new(path))?;
    } else if let Some(hex) = matches.value_of("code") {
        if hex.len() % 2 != 0 {
            return Err(Box::new(AppError {
                why: String::from("The hex string must contain an even number of bytes"),
            }));
        }

        code = get_code_from_str(hex)?;
    } else {
        unreachable!();
    }

    for i in (0..code.len()).step_by(2) {
        let opcode = [code[i], code[i + 1]];
        match decoder::decode(&opcode) {
            Some(ins) => println!("{:#08x}: {:02x}{:02x} {}", i, opcode[0], opcode[1], ins),
            None => println!(
                "{:#08x}: {:02x}{:02x} INVALID OPCODE",
                i, opcode[0], opcode[1]
            ),
        }
    }

    Ok(())
}
