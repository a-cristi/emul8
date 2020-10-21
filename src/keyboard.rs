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
            let key = self.get_key();
                
            if let Some(key) = key {
                // If we have a key return it now.
                return key;
            }

            // No key press yet, wait for the user to press it.
            // TODO: can we do better than a busy loop?
            std::thread::yield_now();
        }
    }

    fn get_key(&mut self) -> Option<EmuKey> {
        // Get access to the keyboard.
        let mut kbd = self.state.lock().unwrap();

        if kbd.stop && kbd.key.is_none() {
            // If we must stop but we don't have a key return `0`. 
            // It should not matter what we reurn since we will stop emulation anyway.
            Some(EmuKey::new(0))
        } else {
            // This will leave a `None`, so the next instruction isn't affected by the currently pressed key. Not quite perfect.
            kbd.key.take()
        }

    }
}
