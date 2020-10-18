use instruction_emulator::EmuKey;
use std::sync::Arc;
use std::sync::Mutex;

/// The underlaying keyboard state.
pub struct KeyboardState {
    // Holds the last pressed key until it is replaced or consumed. If no key was pressed it is `None`.
    pub key: Option<EmuKey>,

    /// If `true`, will stop waiting for a key and will return immediately.
    pub stop: bool,
}

impl Default for KeyboardState {
    fn default() -> Self {
        // By default no key is pressed.
        KeyboardState {
            key: None,
            stop: false,
        }
    }
}

/// Describes the CHIP8 screen as used by `instruction_emulator`.
pub struct Keyboard {
    /// The keyboard state. This is shared between the emulation layer and the user interaction layer.
    state: Arc<Mutex<KeyboardState>>,
}

impl Keyboard {
    pub fn new(state: Arc<Mutex<KeyboardState>>) -> Self {
        Self { state }
    }
}

impl instruction_emulator::EmuKeyboard for Keyboard {
    fn wait_for_keypress(&mut self) -> EmuKey {
        loop {
            {
                // Get access to the keyboard.
                let mut kbd = self.state.lock().unwrap();

                if kbd.stop {
                    return EmuKey::new(0);
                }

                if let Some(key) = kbd.key {
                    // If we have a key return it and store `None` in its place.
                    kbd.key = None;
                    return key;
                }
            }

            // No key press yet, wait for the user to press it.
            // TODO: can we do better than a busy loop?
            std::sync::atomic::spin_loop_hint();
        }
    }
}
