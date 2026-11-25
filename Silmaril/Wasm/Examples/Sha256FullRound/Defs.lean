module

public import Silmaril.Wasm.Examples.Sha256Round.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Logic.Memory.Defs

/-! The C wrapper's eight-word output ABI and the three exact linked bodies.
The destination is an i32 address into the instance's memory 0. -/
@[expose] public section
namespace Silmaril.Wasm.Examples.Sha256FullRound

open Silmaril.Crypto.SHA256.Kernel (Word round)
open Execution Execution.Core Validation
open Logic.Core (Region bytesAt)

abbrev Input := Sha256Round.Input

/-- The freestanding Clang/LLD wasm32 output. -/
def fixture : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x27, 0x03, 0x60,
  0x09, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x01, 0x7f,
  0x60, 0x07, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x01, 0x7f, 0x60,
  0x0b, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f,
  0x00, 0x03, 0x04, 0x03, 0x00, 0x01, 0x02, 0x05, 0x03, 0x01, 0x00, 0x02,
  0x06, 0x08, 0x01, 0x7f, 0x01, 0x41, 0x80, 0x88, 0x04, 0x0b, 0x07, 0x19,
  0x02, 0x06, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00, 0x0c, 0x73,
  0x68, 0x61, 0x32, 0x35, 0x36, 0x5f, 0x72, 0x6f, 0x75, 0x6e, 0x64, 0x00,
  0x02, 0x0a, 0xe4, 0x01, 0x03, 0x49, 0x00, 0x20, 0x01, 0x20, 0x00, 0x72,
  0x20, 0x02, 0x71, 0x20, 0x01, 0x20, 0x00, 0x71, 0x72, 0x20, 0x00, 0x41,
  0x1e, 0x77, 0x20, 0x00, 0x41, 0x13, 0x77, 0x73, 0x20, 0x00, 0x41, 0x0a,
  0x77, 0x73, 0x6a, 0x20, 0x06, 0x6a, 0x20, 0x03, 0x41, 0x1a, 0x77, 0x20,
  0x03, 0x41, 0x15, 0x77, 0x73, 0x20, 0x03, 0x41, 0x07, 0x77, 0x73, 0x6a,
  0x20, 0x07, 0x6a, 0x20, 0x05, 0x20, 0x04, 0x73, 0x20, 0x03, 0x71, 0x20,
  0x05, 0x73, 0x6a, 0x20, 0x08, 0x6a, 0x0b, 0x2b, 0x00, 0x20, 0x04, 0x20,
  0x00, 0x6a, 0x20, 0x01, 0x41, 0x1a, 0x77, 0x20, 0x01, 0x41, 0x15, 0x77,
  0x73, 0x20, 0x01, 0x41, 0x07, 0x77, 0x73, 0x6a, 0x20, 0x05, 0x6a, 0x20,
  0x03, 0x20, 0x02, 0x73, 0x20, 0x01, 0x71, 0x20, 0x03, 0x73, 0x6a, 0x20,
  0x06, 0x6a, 0x0b, 0x6c, 0x01, 0x01, 0x7f, 0x20, 0x01, 0x20, 0x02, 0x20,
  0x03, 0x20, 0x05, 0x20, 0x06, 0x20, 0x07, 0x20, 0x08, 0x20, 0x09, 0x20,
  0x0a, 0x10, 0x80, 0x80, 0x80, 0x80, 0x00, 0x21, 0x0b, 0x20, 0x00, 0x20,
  0x03, 0x36, 0x02, 0x0c, 0x20, 0x00, 0x20, 0x02, 0x36, 0x02, 0x08, 0x20,
  0x00, 0x20, 0x01, 0x36, 0x02, 0x04, 0x20, 0x00, 0x20, 0x0b, 0x36, 0x02,
  0x00, 0x20, 0x04, 0x20, 0x05, 0x20, 0x06, 0x20, 0x07, 0x20, 0x08, 0x20,
  0x09, 0x20, 0x0a, 0x10, 0x81, 0x80, 0x80, 0x80, 0x00, 0x21, 0x0a, 0x20,
  0x00, 0x20, 0x07, 0x36, 0x02, 0x1c, 0x20, 0x00, 0x20, 0x06, 0x36, 0x02,
  0x18, 0x20, 0x00, 0x20, 0x05, 0x36, 0x02, 0x14, 0x20, 0x00, 0x20, 0x0a,
  0x36, 0x02, 0x10, 0x0b
]⟩

def eSignature : RecType := ⟨[⟨true, [], .func ⟨List.replicate 7 .i32, [.i32]⟩⟩]⟩
def roundSignature : RecType := ⟨[⟨true, [], .func ⟨List.replicate 11 .i32, []⟩⟩]⟩

def eBody : Expr :=
  let get (i : Fin (2 ^ 32)) := Instr.localGet ⟨i⟩
  let push := Instr.intConst .i32
  let bin := Instr.intBinOp .i32
  [get 4, get 0, bin .add, get 1, push 26, bin .rotl,
   get 1, push 21, bin .rotl, bin .xor, get 1, push 7, bin .rotl, bin .xor, bin .add,
   get 5, bin .add, get 3, get 2, bin .xor, get 1, bin .and, get 3, bin .xor, bin .add,
   get 6, bin .add]

def aLocals : List LocalIdx := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨9⟩, ⟨10⟩]
def eLocals : List LocalIdx := [⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨9⟩, ⟨10⟩]

/-- Each entry pairs an output word slot with the local supplying that word. -/
abbrev Destination := Fin 8 × LocalIdx

def firstWrites : List Destination := [(3, ⟨3⟩), (2, ⟨2⟩), (1, ⟨1⟩), (0, ⟨11⟩)]
def finalWrites : List Destination := [(7, ⟨7⟩), (6, ⟨6⟩), (5, ⟨5⟩), (4, ⟨10⟩)]

def storeInstr (slot : Fin 8) : Instr :=
  .intStore .i32 none ⟨0⟩ ⟨2, Fin.ofNat _ (4 * slot.val)⟩

def stores (targets : List Destination) : Expr :=
  targets.flatMap fun (slot, source) => [.localGet ⟨0⟩, .localGet source, storeInstr slot]

def computeA : Expr := aLocals.map Instr.localGet ++ [.call ⟨0⟩, .localSet ⟨11⟩]
def computeE : Expr := eLocals.map Instr.localGet ++ [.call ⟨1⟩, .localSet ⟨10⟩]

def roundBody : Expr := computeA ++ stores firstWrites ++ computeE ++ stores finalWrites

def aFunction : Func := ⟨⟨0⟩, [], Sha256Round.body⟩
def eFunction : Func := ⟨⟨1⟩, [], eBody⟩
def roundFunction : Func := ⟨⟨2⟩, [.i32], roundBody⟩

structure Shape where
  types : List RecType
  funcs : List Func
  memories : List MemoryType
  exports : List Export

def decodeShape? (bytes : ByteArray) : Option Shape := do
  let m ← (Binary.Core.Decode.decodeModule bytes).toOption
  if !m.imports.isEmpty || m.start.isSome then none
  else some ⟨m.types, m.funcs, m.memories, m.exports⟩

def artifactShape : Shape :=
  ⟨[Sha256Round.signature, eSignature, roundSignature], [aFunction, eFunction, roundFunction],
    [⟨.i32, ⟨2, none⟩⟩], [⟨"memory", .memory ⟨0⟩⟩, ⟨"sha256_round", .func ⟨2⟩⟩]⟩

def aValues (x : Input) : List Val :=
  [x.a, x.b, x.c, x.e, x.f, x.g, x.h, x.k, x.w].map Val.i32

def eValues (x : Input) (d : Word) : List Val :=
  [d, x.e, x.f, x.g, x.h, x.k, x.w].map Val.i32

def roundValues (dst : Word) (x : Input) (d : Word) : List Val :=
  [dst, x.a, x.b, x.c, d, x.e, x.f, x.g, x.h, x.k, x.w].map Val.i32

def eEntry {H : Type} (x : Input) (d : Word) (s : Store H) (mi : ModuleInst) : Config H :=
  ⟨s, Frame.forCall mi (eValues x d) [], expression eBody⟩

/-- The eight FIPS working words in their ABI order. -/
def outputWords (x : Input) (d : Word) : Vector Word 8 :=
  let (a, b, c, d, e, f, g, h) := round x.a x.b x.c d x.e x.f x.g x.h x.k x.w
  #v[a, b, c, d, e, f, g, h]

def writeWord (dst : Nat) (word : Fin 8 × Word) (mem : ByteArray) : ByteArray :=
  Memory.writeSlice mem (dst + 4 * word.1.val) (Memory.encodeLE 4 word.2.toNat)

def writeWords (dst : Nat) (words : List (Fin 8 × Word)) (mem : ByteArray) : ByteArray :=
  words.foldl (fun bytes word => writeWord dst word bytes) mem

def slotWords (writes : List Destination) (output : Vector Word 8) : List (Fin 8 × Word) :=
  writes.map fun (slot, _) => (slot, output[slot])

def roundMemory (dst : Nat) (output : Vector Word 8) (mem : ByteArray) : ByteArray :=
  writeWords dst (slotWords (firstWrites ++ finalWrites) output) mem

/-- The eight little-endian words and the byte frame of the output buffer. -/
structure OutputOk (before after : ByteArray) (dst : Nat) (words : Vector Word 8) : Prop where
  size_eq : after.size = before.size
  readBack : ∀ slot : Fin 8, Memory.load after (dst + 4 * slot.val) 4 = some words[slot]
  outside : ∀ region, Region.Disjoint ⟨dst, 32⟩ region → bytesAt after region = bytesAt before region

def aInstance {H : Type} (mi : ModuleInst) : FuncInst H :=
  ⟨.defn (liftRec Sha256Round.signature) 0, mi, .wasm aFunction⟩

def eInstance {H : Type} (mi : ModuleInst) : FuncInst H :=
  ⟨.defn (liftRec eSignature) 0, mi, .wasm eFunction⟩

def roundInstance {H : Type} (mi : ModuleInst) : FuncInst H :=
  ⟨.defn (liftRec roundSignature) 0, mi, .wasm roundFunction⟩

/-- Runtime slots for the two direct calls in the wrapper. -/
structure Linkage {H : Type} (s : Store H) (mi : ModuleInst) where
  aAddress : Nat
  eAddress : Nat
  aSlot : mi.funcs[0]? = some aAddress
  eSlot : mi.funcs[1]? = some eAddress
  aCode : s.funcs[aAddress]? = some (aInstance mi)
  eCode : s.funcs[eAddress]? = some (eInstance mi)

def wrapperFrame (dst : Word) (x : Input) (d : Word) (mi : ModuleInst) : Frame :=
  Frame.forCall mi (roundValues dst x d) roundFunction.locals

def frameAfterA (dst : Word) (x : Input) (d : Word) (mi : ModuleInst) : Frame :=
  (wrapperFrame dst x d mi).setLocal ⟨11⟩ (.i32 (outputWords x d)[0])

def frameAfterE (dst : Word) (x : Input) (d : Word) (mi : ModuleInst) : Frame :=
  (frameAfterA dst x d mi).setLocal ⟨10⟩ (.i32 (outputWords x d)[4])

def memoryAfterA (dst : Word) (x : Input) (d : Word) (mem : MemInst) : MemInst :=
  { mem with bytes := writeWords dst.toNat (slotWords firstWrites (outputWords x d)) mem.bytes }

end Silmaril.Wasm.Examples.Sha256FullRound
