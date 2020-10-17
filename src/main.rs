use clap::{App, Arg};
use cursive;
use cursive::event::{Event, EventResult};
use cursive::theme::BaseColor;
use cursive::theme::Color;
use cursive::theme::ColorStyle;
use cursive::views::Canvas;
use instruction_emulator as emu;
use instruction_emulator::EmuKey;
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

struct RenderState {
    screen_state: Arc<Mutex<screen::ScreenState>>,
    keyboard_state: Arc<Mutex<keyboard::KeyboardState>>,
    screen_width: usize,
    screen_height: usize,
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

    // State shared between the emulator and the UI.
    let screen_state = Arc::new(Mutex::new(screen::ScreenState::default()));
    let keyboard_state = Arc::new(Mutex::new(keyboard::KeyboardState::default()));
    // Set to `true` by `ui_thread` when the user wants to quit. Checked by `emu_thread` to know when to stop emulation.
    let quit = Arc::new(Mutex::new(false));
    // Set to `true` by `ui_thread` when it is safe for `emu_thread` to start emulation.
    let ready = Arc::new(Mutex::new(false));

    // Clone the shared state for the emulator thread.
    let screen_state_emu = screen_state.clone();
    let keyboard_state_emu = keyboard_state.clone();
    let quit_emu = quit.clone();
    let ready_emu = ready.clone();

    let emu_thread = std::thread::spawn(move || {
        // Create the scrren, keyboard and memnory that will be used by the emulator.
        let mut screen = screen::Screen::new(screen_state_emu);
        let mut keyboard = keyboard::Keyboard::new(keyboard_state_emu);
        let mut memory = memory::Memory::default();

        // Load the program into memory.
        memory.load_program(&code).unwrap();
        // Load the fonts into memory.
        memory.load_fonts(&fonts::get_fonts()).unwrap();

        // Create the emulator.
        let mut emu = emu::InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        // Check if the `ui_thread` signaled us to start.
        while !*ready_emu.lock().unwrap() {}

        loop {
            // Should we stop?
            if *quit_emu.clone().lock().unwrap() {
                break;
            }

            // Decrement the timers. This should be done at 60Hz/s.
            emu.decrement_timers();
            // Emulate the next instruction.
            match emu.emulate_next() {
                Ok(_) => (),
                Err(_) => {
                    // TODO: handle errors here.
                    break;
                }
            }

            // Sleep a little.
            // TODO: keep a ~stady FPS
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
    });

    let ui_thread = std::thread::spawn(move || {
        let rs = RenderState {
            screen_state: screen_state.clone(),
            keyboard_state: keyboard_state.clone(),
            screen_width: screen::DEFAULT_SCREEN_WIDTH,
            screen_height: screen::DEFAULT_SCREEN_HEIGHT,
        };

        let mut siv = cursive::default();

        siv.add_global_callback('q', |s| s.quit());

        siv.add_layer(
            Canvas::new(rs)
                .with_required_size(|rs: &mut RenderState, _| {
                    (rs.screen_width, rs.screen_height).into()
                })
                .with_draw(|rs: &RenderState, printer| {
                    let ss = rs.screen_state.lock().unwrap();
                    for row in 0..ss.height {
                        for col in 0..ss.width {
                            let new = ss.buffer[col + row * ss.width];
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
                })
                .with_on_event(|rs: &mut RenderState, event| match event {
                    Event::Char(c) => {
                        let digit = c.to_digit(16);
                        if let Some(digit) = digit {
                            if digit < 16 {
                                let mut kbd = rs.keyboard_state.lock().unwrap();
                                kbd.key = Some(EmuKey::new(digit as u8));
                                return EventResult::Consumed(None);
                            }
                        }
                        EventResult::Ignored
                    }
                    _ => EventResult::Ignored,
                }),
        );

        siv.refresh();

        let ready = ready.clone();
        {
            let mut ready = ready.lock().unwrap();
            *ready = true;
        }

        let quit = quit.clone();
        loop {
            siv.step();

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
                let mut quit = quit.lock().unwrap();
                *quit = true;
                break;
            }
        }
    });

    // TODO: handle errors here
    match ui_thread.join() {
        Err(_e) => (),
        _ => (),
    }

    match emu_thread.join() {
        Err(_e) => (),
        _ => (),
    }
}
