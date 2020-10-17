use std::sync::Arc;
use std::sync::Mutex;

/// The underlaying keyboard state.
pub struct KeyboardState {
    // Holds the last pressed key until it is replaced or consumed. If no key was pressed it is `None`.
    key: Option<u8>,
}

impl Default for KeyboardState {
    fn default() -> Self {
        // By default no key is pressed.
        KeyboardState { key: None }
    }
}

/// Describes the CHIP8 screen as used by `instruction_emulator`.
pub struct Keyboard {
    /// The keyboard state. This is shared between the emulation layer and the user interaction layer.
    data: Arc<Mutex<KeyboardState>>,
}

impl Default for Keyboard {
    fn default() -> Self {
        Keyboard {
            data: Arc::new(Mutex::new(KeyboardState::default())),
        }
    }
}

impl instruction_emulator::EmuKeyboard for Keyboard {
    fn wait_for_keypress(&mut self) -> u8 {
        loop {
            {
                // Get access to the keyboard.
                let mut kbd = self.data.lock().unwrap();
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
