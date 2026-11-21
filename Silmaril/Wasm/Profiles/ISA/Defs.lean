module

public import Silmaril.Wasm.Profiles.Defs
public import Silmaril.Wasm.Tools.Meta.Leb.Defs

@[expose] public section

namespace Silmaril.Wasm.Profiles.ISA

open Validation Models

/-- Prefix spaces, not a claim that all of them are accepted by Core. -/
inductive Prefix where
  | gc | misc | simd | atomic
  deriving DecidableEq, Repr

def Prefix.byte : Prefix → UInt8
  | .gc => 0xfb
  | .misc => 0xfc
  | .simd => 0xfd
  | .atomic => 0xfe

inductive Opcode where
  | primary (byte : UInt8)
  | prefixed (space : Prefix) (index : UInt32)
  deriving DecidableEq, Repr

/-- Only the canonical opcode bytes; no instruction immediates are encoded here. -/
def Opcode.bytes : Opcode → List UInt8
  | .primary byte => [byte]
  | .prefixed space index => space.byte :: Tools.Meta.encU32 index.toNat

/-- A closed slice without immediates. The last case is a GC operation, not arithmetic. -/
inductive Flat where
  | add32 | add64 | divS32 | divU32 | divS64 | divU64
  | extend32S64 | truncSatS32F32 | truncSatU32F32 | refI31
  deriving DecidableEq, Repr

def Flat.all : List Flat :=
  [.add32, .add64, .divS32, .divU32, .divS64, .divU64, .extend32S64,
    .truncSatS32F32, .truncSatU32F32, .refI31]

def Flat.opcode : Flat → Opcode
  | .add32 => .primary 0x6a
  | .add64 => .primary 0x7c
  | .divS32 => .primary 0x6d
  | .divU32 => .primary 0x6e
  | .divS64 => .primary 0x7f
  | .divU64 => .primary 0x80
  | .extend32S64 => .primary 0xc4
  | .truncSatS32F32 => .prefixed .misc 0
  | .truncSatU32F32 => .prefixed .misc 1
  | .refI31 => .prefixed .gc 28

def Flat.lookup? (opcode : Opcode) : Option Flat := all.find? fun instr => decide (instr.opcode = opcode)

def Flat.inputs : Flat → List CValType
  | .add32 | .divS32 | .divU32 => [.i32, .i32]
  | .add64 | .divS64 | .divU64 => [.i64, .i64]
  | .extend32S64 => [.i64]
  | .truncSatS32F32 | .truncSatU32F32 => [.num (.float .f32)]
  | .refI31 => [.i32]

def Flat.outputs : Flat → List CValType
  | .add32 | .divS32 | .divU32 | .truncSatS32F32 | .truncSatU32F32 => [.i32]
  | .add64 | .divS64 | .divU64 | .extend32S64 => [.i64]
  | .refI31 => [.refT false (.abs .i31)]

/-- Typed flat syntax: the tag determines the complete input and output stacks. -/
inductive Flat.At : List CValType → List CValType → Type where
  | exact (tag : Flat) : At tag.inputs tag.outputs

inductive Binop where
  | add
  | div (sign : Signedness)
  deriving DecidableEq, Repr

def Binop.toCore : Binop → IntBinOp
  | .add => .add
  | .div sign => .div sign

/-- Factored syntax, indexed by exact stack effects. `extend32S64` has no
width argument because an `i32.extend32_s` would not be a Wasm instruction. -/
inductive Op : List CValType → List CValType → Type where
  | bin (width : IntType) (op : Binop) : Op [.num (.int width), .num (.int width)] [.num (.int width)]
  | extend32S64 : Op [.i64] [.i64]
  | truncSat (sign : Signedness) : Op [.num (.float .f32)] [.i32]
  | refI31 : Op [.i32] [.refT false (.abs .i31)]

abbrev SomeOp := Σ inputs, Σ outputs, Op inputs outputs

/-- Factored syntax without stack indices. -/
inductive RawOp where
  | bin (width : IntType) (op : Binop)
  | extend32S64
  | truncSat (sign : Signedness)
  | refI31

def RawOp.infer : RawOp → SomeOp
  | .bin width op => ⟨_, _, .bin width op⟩
  | .extend32S64 => ⟨_, _, .extend32S64⟩
  | .truncSat sign => ⟨_, _, .truncSat sign⟩
  | .refI31 => ⟨_, _, .refI31⟩

def Op.forget {inputs outputs} : Op inputs outputs → RawOp
  | .bin width op => .bin width op
  | .extend32S64 => .extend32S64
  | .truncSat sign => .truncSat sign
  | .refI31 => .refI31

def Flat.typed : (tag : Flat) → Op tag.inputs tag.outputs
  | .add32 => .bin .i32 .add
  | .add64 => .bin .i64 .add
  | .divS32 => .bin .i32 (.div .signed)
  | .divU32 => .bin .i32 (.div .unsigned)
  | .divS64 => .bin .i64 (.div .signed)
  | .divU64 => .bin .i64 (.div .unsigned)
  | .extend32S64 => .extend32S64
  | .truncSatS32F32 => .truncSat .signed
  | .truncSatU32F32 => .truncSat .unsigned
  | .refI31 => .refI31

def Flat.At.toOp {inputs outputs} : Flat.At inputs outputs → Op inputs outputs
  | .exact tag => tag.typed

def Flat.At.tag {inputs outputs} : Flat.At inputs outputs → Flat
  | .exact tag => tag

def Op.toFlat {inputs outputs} : Op inputs outputs → Flat.At inputs outputs
  | .bin .i32 .add => .exact .add32
  | .bin .i64 .add => .exact .add64
  | .bin .i32 (.div .signed) => .exact .divS32
  | .bin .i32 (.div .unsigned) => .exact .divU32
  | .bin .i64 (.div .signed) => .exact .divS64
  | .bin .i64 (.div .unsigned) => .exact .divU64
  | .extend32S64 => .exact .extend32S64
  | .truncSat .signed => .exact .truncSatS32F32
  | .truncSat .unsigned => .exact .truncSatU32F32
  | .refI31 => .exact .refI31

def Op.tag {inputs outputs} (op : Op inputs outputs) : Flat := op.toFlat.tag

def Op.erase {inputs outputs} : Op inputs outputs → Instr
  | .bin width op => .intBinOp width op.toCore
  | .extend32S64 => .intUnOp .i64 (.extend .i32)
  | .truncSat sign => .convert (.truncSat .f32 .i32 sign)
  | .refI31 => .refI31

def Flat.erase (tag : Flat) : Instr := tag.typed.erase

def Flat.pack (tag : Flat) : SomeOp := ⟨tag.inputs, tag.outputs, tag.typed⟩

def RawOp.erase (op : RawOp) : Instr := op.infer.2.2.erase

def Flat.use (S : FeatureSet) (tag : Flat) : Prop := Instr.InFeat S tag.erase

instance (S : FeatureSet) (tag : Flat) : Decidable (tag.use S) := inferInstanceAs (Decidable (Instr.InFeat S tag.erase))

abbrev Admitted (W : Type) [HasFeatures W] := { tag : Flat // tag.use (HasFeatures.features W) }

def Admitted.lookup? (W : Type) [HasFeatures W] (opcode : Opcode) : Option (Admitted W) := do
  let tag ← Flat.lookup? opcode
  if h : tag.use (HasFeatures.features W) then some ⟨tag, h⟩ else none

end Silmaril.Wasm.Profiles.ISA
