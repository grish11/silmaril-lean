module

public import Silmaril.Machine.CBackend.RTL.SSA.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Defs

/-! # A three-word ABI for a checked counted PEG loop -/

@[expose] public section

namespace Silmaril.Machine.PEG.CountedLoop

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.RTL.SSA (Block Func Prog)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature i1)
open Silmaril.MLIR.SCF (While)

abbrev i64 : Width := ⟨64, by decide⟩
abbrev Bank := [i64, i64, i64]

def bank (count left right : Word) : Env Bank :=
  .cons count (.cons left (.cons right .nil))

/-- Function arguments and results are respectively the remaining count,
left accumulator and right accumulator, one word per register. -/
def words : Env Bank → List Word
  | .cons count (.cons left (.cons right .nil)) => [count, left, right]

def fromWords : List Word → Option (Env Bank)
  | [count, left, right] => some (bank count left right)
  | _ => none

/-- The admitted SCF instruction and edge shape. The typed scopes guarantee
that the add reads both old accumulators. Its result and the old right
accumulator are passed together alongside the decremented counter. -/
def source {Op : OpSignature}
    (nonzero : Op [i64] i1) (pred : Op [i64] i64) (add : Op [i64, i64] i64) :
    While Op Bank Bank where
  State := Bank
  Payload := Bank
  init := .cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))
  before := .letOp nonzero (.cons .here .nil) <|
    .terminator (.condition .here
      (.cons (.there .here) (.cons (.there (.there .here))
        (.cons (.there (.there (.there .here))) .nil))))
  after := .letOp pred (.cons .here .nil) <|
    .letOp add (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) <|
    .terminator (.yield (.cons (.there .here)
      (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))))
  cont := .terminator (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))

/-- Disjoint banks give each block its own parameter registers. The
preheader's word constant dominates both loop blocks. -/
inductive Register
  | input (slot : Nat)
  | before (slot : Nat)
  | after (slot : Nat)
  | exit (slot : Nat)
  | one
  | nextCount
  | nextRight
  deriving DecidableEq, Repr

def preheader : Block Register :=
  ⟨[.input 0, .input 1, .input 2], [.const .one 1], .jump 1 [.input 0, .input 1, .input 2]⟩

/-- The i1 comparison and the source conditional fuse to the native
nonzero branch on the original word. Both edges select the old bank. -/
def header : Block Register :=
  ⟨[.before 0, .before 1, .before 2], [],
    .cond (.before 0) 2 [.before 0, .before 1, .before 2] 3 [.before 0, .before 1, .before 2]⟩

def latch : Block Register :=
  ⟨[.after 0, .after 1, .after 2],
    [.binary .sub .nextCount (.after 0) .one, .binary .add .nextRight (.after 1) (.after 2)],
    .jump 1 [.nextCount, .after 2, .nextRight]⟩

def exitBlock : Block Register :=
  ⟨[.exit 0, .exit 1, .exit 2], [], .ret [.exit 0, .exit 1, .exit 2]⟩

def target : Func Register := ⟨⟨3, 3⟩, 0, [preheader, header, latch, exitBlock]⟩

def program : Prog Register := ⟨[target]⟩

/-- Admission is an exact equality of typed SCF syntax. The three opcodes
stay abstract until an interpretation supplies their bitvector semantics. -/
structure Image {Op : OpSignature} (loop : While Op Bank Bank) where
  nonzero : Op [i64] i1
  pred : Op [i64] i64
  add : Op [i64, i64] i64
  shape : loop = source nonzero pred add

/-- The only primitive laws needed for the fusion and the two arithmetic
bindings. The branch reads an i64 directly, with nonzero corresponding to
the true i1 result. -/
structure Image.Agrees {Op : OpSignature} {loop : While Op Bank Bank} (image : Image loop)
    (evalOp : Eval Op) : Prop where
  nonzero : ∀ c : Word, (evalOp image.nonzero (.cons c .nil)).getLsbD 0 = (c != 0)
  pred : ∀ c : Word, evalOp image.pred (.cons c .nil) = c - 1
  add : ∀ x y : Word, evalOp image.add (.cons x (.cons y .nil)) = x + y

def lower {Op : OpSignature} {loop : While Op Bank Bank} (_ : Image loop) : Prog Register := program

abbrev pegSlots {Data : Type} (left right : Data) : List (Silmaril.SSA.PEG.Ty Data) :=
  [.count, .data left, .data right]

/-- The count field of a PEG input is decoded as the unsigned value of
its machine word. Both data fields are modular 64-bit values. -/
def wordProfile (Data : Type) : Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Profile Data :=
  ⟨fun _ => i64, i64⟩

end Silmaril.Machine.PEG.CountedLoop
