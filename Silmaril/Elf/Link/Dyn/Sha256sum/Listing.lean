module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Defs
public import Silmaril.Elf.Link.Dyn.Proc.Defs

/-! # GNU `sha256sum`: code chunks and listings of its startup and shutdown code

GENERATED (untrusted): the bytes are checked against the file and the listings against
`Open9.decode` by `decide +kernel` in `Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Mem`. The chunks
are `.init` (`0x2000`), `.plt.got` (`0x23b0`), the crt code from `_start` to `frame_dummy`
(`0x3a40`, the same instructions as hello-gcc's, gcc's `crtstuff`), and `.fini` (`0x6d44`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86

def shaInitText : List Byte := ([0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x05, 0xd1, 0x7f, 0x00, 0x00, 0x48, 0x85, 0xc0, 0x74, 0x02, 0xff, 0xd0, 0x48, 0x83, 0xc4, 0x08, 0xc3] : List Nat).map (BitVec.ofNat 8)

def shaInitListing : List (Nat × Ext9.Instr × Nat) := [
  (0, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.endbr64)), 4),
  (4, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.aluI8 (Ext.Sz.q) (AluOp.sub) (Ext.RM.reg (Reg.rsp)) 0x08#8)), 4),
  (8, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.load (Ext.Sz.q) (Reg.rax) (Ext.Mem.ofRip 0x00007fd1#32))), 7),
  (15, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.test (Ext.Sz.q) (Ext.RM.reg (Reg.rax)) (Reg.rax))), 3),
  (18, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jcc8 (Ext.Cond.e) 0x02#8)), 2),
  (20, Ext9.Instr.new (Ext9.New.callInd (Ext.RM.reg (Reg.rax))), 2),
  (22, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.aluI8 (Ext.Sz.q) (AluOp.add) (Ext.RM.reg (Reg.rsp)) 0x08#8)), 4),
  (26, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.ret)), 1)]

def shaCrtText : List Byte := ([0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xed, 0x49, 0x89, 0xd1, 0x5e, 0x48, 0x89, 0xe2, 0x48, 0x83, 0xe4, 0xf0, 0x50, 0x54, 0x45, 0x31, 0xc0, 0x31, 0xc9, 0x48, 0x8d, 0x3d, 0xf1, 0xec, 0xff, 0xff, 0xff, 0x15, 0x4b, 0x65, 0x00, 0x00, 0xf4, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0xc1, 0x65, 0x00, 0x00, 0x48, 0x8d, 0x05, 0xba, 0x65, 0x00, 0x00, 0x48, 0x39, 0xf8, 0x74, 0x15, 0x48, 0x8b, 0x05, 0x4e, 0x65, 0x00, 0x00, 0x48, 0x85, 0xc0, 0x74, 0x09, 0xff, 0xe0, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00, 0xc3, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0x91, 0x65, 0x00, 0x00, 0x48, 0x8d, 0x35, 0x8a, 0x65, 0x00, 0x00, 0x48, 0x29, 0xfe, 0x48, 0x89, 0xf0, 0x48, 0xc1, 0xee, 0x3f, 0x48, 0xc1, 0xf8, 0x03, 0x48, 0x01, 0xc6, 0x48, 0xd1, 0xfe, 0x74, 0x14, 0x48, 0x8b, 0x05, 0x1d, 0x65, 0x00, 0x00, 0x48, 0x85, 0xc0, 0x74, 0x08, 0xff, 0xe0, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00, 0xc3, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00, 0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0x3d, 0x55, 0x65, 0x00, 0x00, 0x00, 0x75, 0x2b, 0x55, 0x48, 0x83, 0x3d, 0xb2, 0x64, 0x00, 0x00, 0x00, 0x48, 0x89, 0xe5, 0x74, 0x0c, 0x48, 0x8b, 0x3d, 0x06, 0x65, 0x00, 0x00, 0xe8, 0xa9, 0xe8, 0xff, 0xff, 0xe8, 0x64, 0xff, 0xff, 0xff, 0xc6, 0x05, 0x2d, 0x65, 0x00, 0x00, 0x01, 0x5d, 0xc3, 0x0f, 0x1f, 0x00, 0xc3, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00, 0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x77, 0xff, 0xff, 0xff] : List Nat).map (BitVec.ofNat 8)

def shaCrtListing : List (Nat × Ext9.Instr × Nat) := [
  (0, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.endbr64)), 4),
  (4, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.alu (Ext.Sz.d) (AluOp.xor) (Ext.RM.reg (Reg.rbp)) (Reg.rbp))), 2),
  (6, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.mov (Ext.Sz.q) (Ext.RM.reg (Reg.r9)) (Reg.rdx))), 3),
  (9, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.pop (Reg.rsi))), 1),
  (10, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.mov (Ext.Sz.q) (Ext.RM.reg (Reg.rdx)) (Reg.rsp))), 3),
  (13, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.aluI8 (Ext.Sz.q) (AluOp.and) (Ext.RM.reg (Reg.rsp)) 0xf0#8)), 4),
  (17, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.push (Reg.rax))), 1),
  (18, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.push (Reg.rsp))), 1),
  (19, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.alu (Ext.Sz.d) (AluOp.xor) (Ext.RM.reg (Reg.r8)) (Reg.r8))), 3),
  (22, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.alu (Ext.Sz.d) (AluOp.xor) (Ext.RM.reg (Reg.rcx)) (Reg.rcx))), 2),
  (24, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.lea (Ext.Sz.q) (Reg.rdi) (Ext.Mem.ofRip 0xffffecf1#32))), 7),
  (31, Ext9.Instr.new (Ext9.New.callInd (Ext.RM.mem (Ext.Mem.ofRip 0x0000654b#32))), 6),
  (38, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 9)), 10),
  (48, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.lea (Ext.Sz.q) (Reg.rdi) (Ext.Mem.ofRip 0x000065c1#32))), 7),
  (55, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.lea (Ext.Sz.q) (Reg.rax) (Ext.Mem.ofRip 0x000065ba#32))), 7),
  (62, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.alu (Ext.Sz.q) (AluOp.cmp) (Ext.RM.reg (Reg.rax)) (Reg.rdi))), 3),
  (65, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jcc8 (Ext.Cond.e) 0x15#8)), 2),
  (67, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.load (Ext.Sz.q) (Reg.rax) (Ext.Mem.ofRip 0x0000654e#32))), 7),
  (74, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.test (Ext.Sz.q) (Ext.RM.reg (Reg.rax)) (Reg.rax))), 3),
  (77, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jcc8 (Ext.Cond.e) 0x09#8)), 2),
  (79, Ext9.Instr.new (Ext9.New.jmpInd (Ext.RM.reg (Reg.rax))), 2),
  (81, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 6)), 7),
  (88, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.ret)), 1),
  (89, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 6)), 7),
  (96, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.lea (Ext.Sz.q) (Reg.rdi) (Ext.Mem.ofRip 0x00006591#32))), 7),
  (103, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.lea (Ext.Sz.q) (Reg.rsi) (Ext.Mem.ofRip 0x0000658a#32))), 7),
  (110, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.alu (Ext.Sz.q) (AluOp.sub) (Ext.RM.reg (Reg.rsi)) (Reg.rdi))), 3),
  (113, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.mov (Ext.Sz.q) (Ext.RM.reg (Reg.rax)) (Reg.rsi))), 3),
  (116, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.shift (Ext.Sz.q) (Ext.ShiftOp.shr) (Ext.RM.reg (Reg.rsi)) (Ext.Count.imm 0x3f#8))), 4),
  (120, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.shift (Ext.Sz.q) (Ext.ShiftOp.sar) (Ext.RM.reg (Reg.rax)) (Ext.Count.imm 0x03#8))), 4),
  (124, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.alu (Ext.Sz.q) (AluOp.add) (Ext.RM.reg (Reg.rsi)) (Reg.rax))), 3),
  (127, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.shift (Ext.Sz.q) (Ext.ShiftOp.sar) (Ext.RM.reg (Reg.rsi)) (Ext.Count.one))), 3),
  (130, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jcc8 (Ext.Cond.e) 0x14#8)), 2),
  (132, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.load (Ext.Sz.q) (Reg.rax) (Ext.Mem.ofRip 0x0000651d#32))), 7),
  (139, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.test (Ext.Sz.q) (Ext.RM.reg (Reg.rax)) (Reg.rax))), 3),
  (142, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jcc8 (Ext.Cond.e) 0x08#8)), 2),
  (144, Ext9.Instr.new (Ext9.New.jmpInd (Ext.RM.reg (Reg.rax))), 2),
  (146, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 5)), 6),
  (152, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.ret)), 1),
  (153, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 6)), 7),
  (160, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.endbr64)), 4),
  (164, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.cmpI8 (Ext.RM.mem (Ext.Mem.ofRip 0x00006555#32)) 0x00#8)), 7),
  (171, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jcc8 (Ext.Cond.ne) 0x2b#8)), 2),
  (173, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.push (Reg.rbp))), 1),
  (174, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.aluI8 (Ext.Sz.q) (AluOp.cmp) (Ext.RM.mem (Ext.Mem.ofRip 0x000064b2#32)) 0x00#8)), 8),
  (182, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.mov (Ext.Sz.q) (Ext.RM.reg (Reg.rbp)) (Reg.rsp))), 3),
  (185, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jcc8 (Ext.Cond.e) 0x0c#8)), 2),
  (187, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.load (Ext.Sz.q) (Reg.rdi) (Ext.Mem.ofRip 0x00006506#32))), 7),
  (194, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.call 0xffffe8a9#32)), 5),
  (199, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.call 0xffffff64#32)), 5),
  (204, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.movI8 (Ext.RM.mem (Ext.Mem.ofRip 0x0000652d#32)) 0x01#8)), 7),
  (211, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.pop (Reg.rbp))), 1),
  (212, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.ret)), 1),
  (213, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 2)), 3),
  (216, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.ret)), 1),
  (217, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 6)), 7),
  (224, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.endbr64)), 4),
  (228, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.jmp 0xffffff77#32)), 5)]

def shaFiniText : List Byte := ([0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x83, 0xc4, 0x08, 0xc3] : List Nat).map (BitVec.ofNat 8)

def shaFiniListing : List (Nat × Ext9.Instr × Nat) := [
  (0, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.endbr64)), 4),
  (4, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.aluI8 (Ext.Sz.q) (AluOp.sub) (Ext.RM.reg (Reg.rsp)) 0x08#8)), 4),
  (8, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.aluI8 (Ext.Sz.q) (AluOp.add) (Ext.RM.reg (Reg.rsp)) 0x08#8)), 4),
  (12, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.ret)), 1)]

def shaPltGotText : List Byte := ([0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0xee, 0x7b, 0x00, 0x00, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00] : List Nat).map (BitVec.ofNat 8)

def shaPltGotListing : List (Nat × Ext9.Instr × Nat) := [
  (0, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.endbr64)), 4),
  (4, Ext9.Instr.new (Ext9.New.jmpInd (Ext.RM.mem (Ext.Mem.ofRip 0x00007bee#32))), 6),
  (10, Ext9.Instr.ext8 (Ext8.Instr.base (Ext.Instr.nop 5)), 6)]

end Silmaril.Elf.Link.Dyn.Sha256sum