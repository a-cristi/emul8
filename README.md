# emul8

Terminal [CHIP8](https://en.wikipedia.org/wiki/CHIP-8) emulator. This is the first project I have written in Rust, and I started it as a learning exercise. It is far from finished.

## Repository structure

* `decoder` - A CHIP8 instruction decoder library.
* `instruction_emulator` - A CHIP8 instruction emulator library.
* `c8d` - A command line utility for disasembling CHIP8 instructions.
* `src` - The sources of the CHIP8 emulator.

## Building

```console
cargo build [--release]
```

## Running

```console
cargo run [--release] -- path/to/rom [--trace path/to/log/file]
# Or
emul8 path/ro/rom [--trace path/to/log/file]
```

If `--trace` is used, each step of the instruction emulator is logeed. Sample output:

```text
00200: a24c LD I, [0x24c]
V0 = 0x00 V1 = 0x00 V2 = 0x00 V3 = 0x00 V4 = 0x00 V5 = 0x00 V6 = 0x00 V7 = 0x00
V8 = 0x00 V9 = 0x00 Va = 0x00 Vb = 0x00 Vc = 0x00 Vd = 0x00 Ve = 0x00 VF = 0x00
PC = 0x000200 SP = 0x00
 I = 0x000000
DT = 0x00 ST = 0x00
00202: 6530 LD V5, 0x30
V0 = 0x00 V1 = 0x00 V2 = 0x00 V3 = 0x00 V4 = 0x00 V5 = 0x00 V6 = 0x00 V7 = 0x00
V8 = 0x00 V9 = 0x00 Va = 0x00 Vb = 0x00 Vc = 0x00 Vd = 0x00 Ve = 0x00 VF = 0x00
PC = 0x000202 SP = 0x00
 I = 0x00024c
DT = 0x00 ST = 0x00
```

This currenlty uses [cursive](https://github.com/gyscos/cursive) with the [crossterm](https://github.com/crossterm-rs/crossterm) backend, simply because it works both in Windows and Linux. I'm thinking about ditching the terminal emulator idea and switching to [SDL2](https://crates.io/crates/sdl2) sometime (or maybe keeping both).

## Missing functionalities

I've mostly tested this against basic ROMs, it is not ready to attempt to run an actual game.

## Resources

* [Cowgod's Chip-8 Technical Reference](http://devernay.free.fr/hacks/chip8/C8TECH10.HTM)
* Some excellent articles by [Craig Thomas](http://craigthomas.ca/tag/chip8.html)
* [Octo](https://github.com/JohnEarnest/Octo)
* The good people at [r/emudev](https://www.reddit.com/r/EmuDev)
