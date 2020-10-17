use clap::{App, Arg};
use cursive;
use cursive::theme::BaseColor;
use cursive::theme::Color;
use cursive::theme::ColorStyle;
use cursive::views::{Canvas};
use instruction_emulator as emu;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::sync::Arc;
use std::sync::Mutex;

mod fonts;
mod keyboard;
mod memory;
mod screen;

fn get_code_from_file(path: &Path) -> std::io::Result<Vec<u8>> {
    let mut file = File::open(path)?;

    let mut contents = Vec::new();
    file.read_to_end(&mut contents)?;

    Ok(contents)
}

struct UiState {
    screen_state: Arc<Mutex<screen::ScreenState>>,
    x: usize,
    y: usize,
}

fn main() {
    let matches = App::new("emul8")
        .version("0.1")
        .author("Cristi")
        .about("CHIP8 emulator")
        .arg(
            Arg::with_name("input")
                .value_name("FILE")
                .help("The file to emulate")
                .takes_value(true)
                .required(true),
        )
        .arg(
            Arg::with_name("FILE")
                .short("t")
                .long("trace")
                .help("Trace execution")
                .takes_value(true)
                .default_value("trace.log"),
        )
        .get_matches();

    let in_path = Path::new(matches.value_of("input").unwrap());
    let code = get_code_from_file(in_path).unwrap();

    let screen_state = Arc::new(Mutex::new(screen::ScreenState::default()));

    let mut memory = memory::Memory::default();
    let mut screen = screen::Screen::new(screen_state.clone());
    let mut keyboard = keyboard::Keyboard::default();

    let mut siv = cursive::default();

    let uis = UiState {
        screen_state: screen_state.clone(),
        x: screen::DEFAULT_SCREEN_WIDTH,
        y: screen::DEFAULT_SCREEN_HEIGHT,
    };

    memory.load_program(&code).unwrap();
    memory.load_fonts(&fonts::get_fonts()).unwrap();

    let mut emu = emu::InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

    siv.add_layer(
        Canvas::new(uis)
            .with_required_size(|ui: &mut UiState, _| (ui.x, ui.y).into())
            .with_draw(|uis: &UiState, printer| {
                let ui = uis.screen_state.lock().unwrap();
                for row in 0..ui.height {
                    for col in 0..ui.width {
                        let new = ui.buffer[col + row * ui.width];
                        let set = new != 0;
                        if set {
                            printer.with_color(
                                ColorStyle::new(
                                    Color::Dark(BaseColor::Red),
                                    Color::Dark(BaseColor::Red),
                                ),
                                |printer| {
                                    printer.print((col, row), " ");
                                },
                            );
                        } else {
                            printer.with_color(
                                ColorStyle::new(
                                    Color::Dark(BaseColor::Black),
                                    Color::Dark(BaseColor::Black),
                                ),
                                |printer| {
                                    printer.print((col, row), " ");
                                },
                            );
                        }
                    }
                }
            }),
    );

    // So we can quit by pressing `q`.
    siv.add_global_callback('q', |s| s.quit());

    siv.refresh();
    // Begin the emulation loop.
    loop {
        siv.step();

        // Emulate the next instruction.
        emu.emulate_next().unwrap();

        let needs_refresh: bool;
        {
            // Get access to the screen state.
            let mut scr_state = screen_state.lock().unwrap();

            // If the screen was update we need a refresh.
            needs_refresh = scr_state.was_updated;

            // Reset the `was_updated` state.
            scr_state.was_updated = false;
        }

        if needs_refresh {
            siv.refresh();
        }

        if !siv.is_running() {
            break;
        }
    }
}
