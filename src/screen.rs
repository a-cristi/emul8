use std::sync::Arc;
use std::sync::Mutex;

/// The default CHIP8 screen is 64 pixels wide.
pub const DEFAULT_SCREEN_WIDTH: usize = 64;

/// The default CHIP8 screen has a height of 32 pixels.
pub const DEFAULT_SCREEN_HEIGHT: usize = 32;

/// The default size of the screen buffer.
const DEFAULT_SCREEN_BUFFER_SIZE: usize = DEFAULT_SCREEN_WIDTH * DEFAULT_SCREEN_HEIGHT;

/// Describes the CHIP8 screen state.
pub struct ScreenState {
    /// The width of the screen.
    pub width: usize,
    /// The height of the screen.
    pub height: usize,
    /// The screen buffer. The buffer size is `width` * `height`.
    /// Each element represents a pixel. The format is:
    ///
    /// ```
    /// (0,      0)     (width,      0)
    ///
    /// (0, height)     (width, height)
    /// ```
    ///
    pub buffer: Vec<u8>,
    /// Set to `true` if at least a pixel changed.
    pub was_updated: bool,
}

impl Default for ScreenState {
    fn default() -> Self {
        ScreenState {
            width: DEFAULT_SCREEN_WIDTH,
            height: DEFAULT_SCREEN_HEIGHT,
            buffer: vec![0; DEFAULT_SCREEN_BUFFER_SIZE],
            was_updated: false,
        }
    }
}

impl ScreenState {
    #[inline]
    fn handle_wraparound(&self, x: u8, y: u8) -> (usize, usize) {
        (x as usize % self.width, y as usize % self.height)
    }

    #[inline]
    fn coordinates_to_index(&self, c: (usize, usize)) -> usize {
        c.0 + c.1 * self.width
    }

    fn clear(&mut self) {
        // TODO: There has to be a better way of doing this.
        self.buffer = vec![0; self.buffer.capacity()];
        self.was_updated = true;
    }

    fn get_pixel(&mut self, x: u8, y: u8) -> Option<u8> {
        let (x, y) = self.handle_wraparound(x, y);
        let index = self.coordinates_to_index((x, y));
        Some(self.buffer[index])
    }

    fn set_pixel(&mut self, x: u8, y: u8, value: u8) -> Option<()> {
        let (x, y) = self.handle_wraparound(x, y);
        let index = self.coordinates_to_index((x, y));
        self.was_updated = self.was_updated || self.buffer[index] != value;
        self.buffer[index] = value;
        Some(())
    }
}

/// Gives access to the CHIP8 screen.
pub struct Screen {
    /// The screen state. This is shared between the emulation layer and the user interaction layer.
    pub state: Arc<Mutex<ScreenState>>,
}

impl Screen {
    pub fn new(state: Arc<Mutex<ScreenState>>) -> Self {
        Screen { state }
    }
}

impl instruction_emulator::EmuScreen for Screen {
    fn clear(&mut self) {
        // Get access to the screen state.
        let mut state = self.state.lock().unwrap();
        state.clear();
    }

    fn get_pixel(&mut self, x: u8, y: u8) -> Option<u8> {
        // Get access to the screen state.
        let mut state = self.state.lock().unwrap();
        state.get_pixel(x, y)
    }

    fn set_pixel(&mut self, x: u8, y: u8, value: u8) -> Option<()> {
        // Get access to the screen state.
        let mut state = self.state.lock().unwrap();
        state.set_pixel(x, y, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clear() {
        let mut screen = ScreenState {
            width: 4,
            height: 1,
            buffer: vec![1; 4],
            was_updated: false,
        };

        let initial_len = screen.buffer.len();
        let initial_cap = screen.buffer.capacity();

        screen.clear();

        assert_eq!(screen.was_updated, true);
        assert_eq!(screen.buffer.len(), initial_len);
        assert_eq!(screen.buffer.capacity(), initial_cap);
        for e in screen.buffer {
            assert_eq!(e, 0);
        }
    }

    #[test]
    fn get_pixel() {
        let width = 4usize;
        let height = 5usize;

        let mut screen = ScreenState {
            width: width,
            height: height,
            buffer: vec![0; width * height],
            was_updated: false,
        };

        for col in 0..width {
            for row in 0..height {
                screen.buffer[col + row * width] = (col + row * width) as u8;
            }
        }

        for col in 0..width {
            for row in 0..height {
                assert_eq!(
                    screen.get_pixel(col as u8, row as u8).unwrap(),
                    (col + row * width) as u8
                );
            }
        }
    }

    #[test]
    fn get_pixel_with_wraparound() {
        let width = 4usize;
        let height = 5usize;

        let mut screen = ScreenState {
            width: width,
            height: height,
            buffer: vec![0; width * height],
            was_updated: false,
        };

        for col in 0..width {
            for row in 0..height {
                screen.buffer[col + row * width] = (col + row * width) as u8;
            }
        }

        assert_eq!(
            screen.get_pixel(0, 6).unwrap(),
            screen.get_pixel(0, (6 % height) as u8).unwrap()
        );
        assert_eq!(screen.was_updated, false);

        assert_eq!(
            screen.get_pixel(7, 4).unwrap(),
            screen.get_pixel((7 % width) as u8, 4).unwrap()
        );
        assert_eq!(screen.was_updated, false);

        assert_eq!(
            screen.get_pixel(17, 14).unwrap(),
            screen
                .get_pixel((17 % width) as u8, (14 % height) as u8)
                .unwrap()
        );
        assert_eq!(screen.was_updated, false);
    }

    #[test]
    fn set_pixel() {
        let width = 4usize;
        let height = 5usize;

        let mut screen = ScreenState {
            width: width,
            height: height,
            buffer: vec![0; width * height],
            was_updated: false,
        };

        for col in 0..width {
            for row in 0..height {
                let value = (col + row * width) as u8;
                screen.set_pixel(col as u8, row as u8, value).unwrap();
                assert_eq!(screen.was_updated, value != 0);
            }
        }

        for col in 0..width {
            for row in 0..height {
                assert_eq!(screen.buffer[col + row * width], (col + row * width) as u8);
            }
        }
    }

    #[test]
    fn set_pixel_with_wraparound() {
        let width = 4usize;
        let height = 5usize;

        let mut screen = ScreenState {
            width: width,
            height: height,
            buffer: vec![0; width * height],
            was_updated: false,
        };

        for col in 0..width {
            for row in 0..height {
                screen.buffer[col + row * width] = (col + row * width) as u8;
            }
        }

        screen.set_pixel(0, 6, 1).unwrap();
        assert_eq!(screen.was_updated, true);

        screen.set_pixel(7, 4, 2).unwrap();
        assert_eq!(screen.was_updated, true);

        screen.set_pixel(17, 14, 3).unwrap();
        assert_eq!(screen.was_updated, true);

        assert_eq!(screen.buffer[0 + (6 % height) * width], 1);
        assert_eq!(screen.buffer[(7 % width) + 4 * width], 2);
        assert_eq!(screen.buffer[(17 % width) + (14 % height) * width], 3);
    }
}
