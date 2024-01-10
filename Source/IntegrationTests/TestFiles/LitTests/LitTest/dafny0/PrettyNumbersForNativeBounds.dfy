// RUN: %testDafnyForEachResolver "%s" -- --show-inference

newtype Small = x: int | -19 <= x < 19
newtype Big = x: int | -19 <= x < 0x1234_5678_9abc_def0
newtype BigHex = x: int | 0xFF <= x < 0x1234_5678_9abc_de00
  witness 0x200

newtype i8 = x: int | -128 <= x < 128
newtype i16 = x: int | -0x8000 <= x < 0x8000
newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype i52 = x: int | -0x10_0000_0000_0000 <= x < 0x10_0000_0000_0000
newtype i64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

newtype u8 = x: int | 0 <= x < 256
newtype u16 = x: int | 0 <= x < 0x1_0000
newtype u32 = x: int | 0 <= x < 0x1_0000_0000
newtype u52 = x: int | 0 <= x < 0x20_0000_0000_0000
newtype u64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

newtype aa = x: int | 0 <= x < 0xFFFA
newtype ab = x: int | 0 <= x < 0xFFFB
newtype ac = x: int | 0 <= x < 0xFFFC
newtype ad = x: int | 0 <= x < 0xFFFD
newtype ae = x: int | 0 <= x < 0xFFFE
newtype af = x: int | 0 <= x < 0xFFFF
newtype a0 = x: int | 0 <= x < 0x1_0000
newtype a1 = x: int | 0 <= x < 0x1_0001
newtype a2 = x: int | 0 <= x < 0x1_0002
newtype a3 = x: int | 0 <= x < 0x1_0003
newtype a4 = x: int | 0 <= x < 0x1_0004
newtype a5 = x: int | 0 <= x < 0x1_0005
newtype a6 = x: int | 0 <= x < 0x1_0006

newtype ba = x: int | -0xFFFA <= x < 0
  witness -1
newtype bb = x: int | -0xFFFB <= x < 0
  witness -1
newtype bc = x: int | -0xFFFC <= x < 0
  witness -1
newtype bd = x: int | -0xFFFD <= x < 0
  witness -1
newtype be = x: int | -0xFFFE <= x < 0
  witness -1
newtype bf = x: int | -0xFFFF <= x < 0
  witness -1
newtype b0 = x: int | -0x1_0000 <= x < 0
  witness -1
newtype b1 = x: int | -0x1_0001 <= x < 0
  witness -1
newtype b2 = x: int | -0x1_0002 <= x < 0
  witness -1
newtype b3 = x: int | -0x1_0003 <= x < 0
  witness -1
newtype b4 = x: int | -0x1_0004 <= x < 0
  witness -1
newtype b5 = x: int | -0x1_0005 <= x < 0
  witness -1
newtype b6 = x: int | -0x1_0006 <= x < 0
  witness -1
