use anyhow;
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
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::sync::Mutex;
use std::thread;

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

fn main() -> anyhow::Result<()> {
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

    // `input` is mandatory, so if we get here we can safely `unwrap` this.
    let in_path = Path::new(matches.value_of("input").unwrap());

    // Read the ROM.
    let code = get_code_from_file(in_path)?;

    // State shared between the emulator and the UI.
    let screen_state = Arc::new(Mutex::new(screen::ScreenState::default()));
    let keyboard_state = Arc::new(Mutex::new(keyboard::KeyboardState::default()));
    // Set to `true` by one of the threads in order to signal to the others that we must exit.
    // Usually, this is done by the `ui_thread` when the user decided to quit, but `emu_thread` can also do it in case of errors.
    let should_stop = Arc::new(AtomicBool::new(false));
    // Set to `true` by `ui_thread` when it is safe for `emu_thread` to start emulation.
    let ready = Arc::new(AtomicBool::new(false));

    // Clone the shared state for the emulator thread.
    let screen_state_emu = screen_state.clone();
    let keyboard_state_emu = keyboard_state.clone();
    let ready_emu = ready.clone();
    let should_stop_emu = should_stop.clone();

    let emu_thread = std::thread::spawn(move || -> anyhow::Result<()> {
        // Create the scrren, keyboard and memnory that will be used by the emulator.
        let mut screen = screen::Screen::new(screen_state_emu);
        let mut keyboard = keyboard::Keyboard::new(keyboard_state_emu);
        let mut memory = memory::Memory::default();

        // Load the program into memory.
        memory.load_program(&code)?;
        // Load the fonts into memory.
        memory.load_fonts(&fonts::get_fonts())?;

        // Create the emulator.
        let mut emu = emu::InstructionEmulator::new(&mut screen, &mut keyboard, &mut memory);

        // Check if the `ui_thread` signaled us to start.
        while !ready_emu.load(Ordering::SeqCst) {
            thread::yield_now();
        }

        loop {
            // Should we stop?
            // TODO: can I relax this and use `Ordering::Relaxed`?
            if should_stop_emu.load(Ordering::SeqCst) {
                return Ok(());
            }

            // Decrement the timers. This should be done at 60Hz/s.
            emu.decrement_timers();
            // Emulate the next instruction.
            match emu.emulate_next() {
                Ok(_) => (),
                Err(e) => {
                    // Signal the other threads that it is time to stop.
                    should_stop_emu.store(true, Ordering::SeqCst);
                    return Err(anyhow::anyhow!("Emulation error: {}", e));
                }
            }

            // Sleep a little.
            // TODO: keep a ~stady FPS
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
    });

    let ui_thread = std::thread::spawn(move || -> anyhow::Result<()> {
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

        // Signal the `emu_thread` that emulation can now begin.
        ready.store(true, Ordering::SeqCst);

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
                // Signal the other threads that is is time to stop.
                should_stop.store(true, Ordering::SeqCst);
                return Ok(());
            }

            // Check if another thread asked us to stop.
            if should_stop.load(Ordering::SeqCst) {
                return Ok(());
            }

            thread::sleep(std::time::Duration::from_millis(2));
        }
    });

    // TODO: a better way of handling errors here?
    ui_thread.join().expect("Could not join the ui thread")?;
    emu_thread
        .join()
        .expect("Could not join the emulation thread")?;

    Ok(())
}
