use clap::{App, Arg};
use cursive::event::{Event, EventResult};
use cursive::theme::{BaseColor, Color, ColorStyle};
use cursive::views::Canvas;
use cursive::Printer;
use instruction_emulator as emu;
use instruction_emulator::EmuKey;
use keyboard::{Keyboard, KeyboardState};
use memory::Memory;
use screen::{Screen, ScreenState};
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

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

fn emulator_loop(
    emulator: &mut emu::InstructionEmulator,
    stop_flag: Arc<AtomicBool>,
    timer_flag: Arc<AtomicBool>,
) -> anyhow::Result<()> {
    // Try to run at 500Hz.
    let expected_duration = Duration::from_millis(1000 / 500);
    loop {
        let start = Instant::now();

        // Should we stop?
        // TODO: can I relax this and use `Ordering::Relaxed`?
        if stop_flag.load(Ordering::SeqCst) {
            return Ok(());
        }

        // If needed decrement the timers.
        if timer_flag.load(Ordering::SeqCst) {
            emulator.decrement_timers();
            // Reset the flag.
            timer_flag.store(false, Ordering::SeqCst);
        }

        // Emulate the next instruction.
        match emulator.emulate_next() {
            Ok(_) => (),
            Err(e) => {
                // Signal the other threads that it is time to stop.
                stop_flag.store(true, Ordering::SeqCst);
                return Err(anyhow::anyhow!("Emulation error: {}", e));
            }
        }

        // Figure out how much time this took.
        let duration = start.elapsed();

        // Try to make each instruction take up to ~2 milis.
        if duration < expected_duration {
            std::thread::sleep(expected_duration - duration);
        }
    }
}

fn handle_draw(render_state: &RenderState, printer: &Printer) {
    let ss = render_state.screen_state.lock().unwrap();
    for row in 0..ss.height {
        for col in 0..ss.width {
            let new = ss.buffer[col + row * ss.width];
            let set = new != 0;
            if set {
                printer.with_color(
                    ColorStyle::new(Color::Dark(BaseColor::Red), Color::Dark(BaseColor::Red)),
                    |printer| {
                        printer.print((col, row), " ");
                    },
                );
            } else {
                printer.with_color(
                    ColorStyle::new(Color::Dark(BaseColor::Black), Color::Dark(BaseColor::Black)),
                    |printer| {
                        printer.print((col, row), " ");
                    },
                );
            }
        }
    }
}

fn handle_event(render_state: &mut RenderState, event: Event) -> EventResult {
    match event {
        Event::Char(c) => {
            let digit = c.to_digit(16);
            if let Some(digit) = digit {
                if digit < 16 {
                    let mut kbd = render_state.keyboard_state.lock().unwrap();
                    kbd.key = Some(EmuKey::new(digit as u8));
                    return EventResult::Consumed(None);
                }
            }
            EventResult::Ignored
        }
        _ => EventResult::Ignored,
    }
}

fn ui_loop(
    screen_state: Arc<Mutex<ScreenState>>,
    keyboard_state: Arc<Mutex<KeyboardState>>,
    ready_flag: Arc<AtomicBool>,
    stop_flag: Arc<AtomicBool>,
) -> anyhow::Result<()> {
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
            .with_draw(|rs: &RenderState, printer| handle_draw(rs, printer))
            .with_on_event(|rs: &mut RenderState, event| handle_event(rs, event)),
    );

    siv.refresh();

    // Signal the `emu_thread` that emulation can now begin.
    ready_flag.store(true, Ordering::SeqCst);

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
            stop_flag.store(true, Ordering::SeqCst);

            // Get access to the keyboard state.
            let mut kbd_state = keyboard_state.lock().unwrap();
            kbd_state.stop = true;

            return Ok(());
        }

        // Check if another thread asked us to stop.
        if stop_flag.load(Ordering::SeqCst) {
            // Get access to the keyboard state.
            let mut kbd_state = keyboard_state.lock().unwrap();
            kbd_state.stop = true;

            return Ok(());
        }
    }
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
            Arg::with_name("trace")
                .value_name("FILE")
                .short("t")
                .long("trace")
                .help("Trace emulation")
                .takes_value(true),
        )
        .get_matches();

    // `input` is mandatory, so if we get here we can safely `unwrap` this.
    let in_path = Path::new(matches.value_of("input").unwrap());

    let emulator_trace_file = match matches.value_of("trace") {
        Some(file_path) => Some(File::create(file_path)?),
        None => None,
    };

    // Read the ROM.
    let code = get_code_from_file(in_path)?;

    // State shared between the emulator and the UI.
    let screen_state = Arc::new(Mutex::new(ScreenState::default()));
    let keyboard_state = Arc::new(Mutex::new(KeyboardState::default()));
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

    // Shared state between the `emu_thread` and the `timer_thread`.
    // Set to `true` when the emulator needs to decrement the timers.
    let decrement_timers = Arc::new(AtomicBool::new(false));
    let decrement_timers_emu = decrement_timers.clone();
    // The timer thread also needs to be stopped when the other threads stop.
    let should_stop_timer = should_stop.clone();

    let timer_thread = thread::Builder::new()
        .name("timer".to_string())
        .spawn(move || {
            loop {
                // Should we stop?
                if should_stop_timer.load(Ordering::SeqCst) {
                    break;
                }

                // Decrement the timers at 60Hz.
                thread::sleep(Duration::from_millis(1000 / 60));
                decrement_timers.store(true, Ordering::SeqCst);

                // Wait until the timers have been decremented.
                while decrement_timers.load(Ordering::SeqCst) {
                    // Should we stop?
                    if should_stop_timer.load(Ordering::SeqCst) {
                        break;
                    }
                    thread::yield_now();
                }
            }
        })?;

    let emu_thread = thread::Builder::new().name("emulator".to_string()).spawn(
        move || -> anyhow::Result<()> {
            // Create the scrren, keyboard and memnory that will be used by the emulator.
            let mut screen = Screen::new(screen_state_emu);
            let mut keyboard = Keyboard::new(keyboard_state_emu);
            let mut memory = Memory::default();

            // Load the program into memory.
            memory.load_program(&code)?;

            // Load the fonts into memory.
            memory.load_fonts(&fonts::get_fonts())?;

            // Create the emulator.
            let mut emu = emu::InstructionEmulator::with_initial_state(
                Default::default(),
                &mut screen,
                &mut keyboard,
                &mut memory,
                emulator_trace_file,
            );

            // Check if the `ui_thread` signaled us to start.
            while !ready_emu.load(Ordering::SeqCst) {
                thread::yield_now();
            }

            emulator_loop(&mut emu, should_stop_emu, decrement_timers_emu)
        },
    )?;

    let ui_thread =
        thread::Builder::new()
            .name("UI".to_string())
            .spawn(move || -> anyhow::Result<()> {
                ui_loop(screen_state, keyboard_state, ready, should_stop)
            })?;

    // TODO: a better way of handling errors here?
    timer_thread
        .join()
        .expect("Could not join the timer thread");
    ui_thread.join().expect("Could not join the ui thread")?;
    emu_thread
        .join()
        .expect("Could not join the emulation thread")?;

    Ok(())
}
