module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Defs

/-! # Split a terminal row with two requests into public dispatcher rows -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests

open LambdaSSA (FiniteCFG Tm Region)
open LetCase.LocallyNameless
open Morphism.CaseSSA (erase)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)

variable {F : Type} {exits captures : Nat}

/-- First supported cut shape. The entry jumps to the sole original block,
which makes two requests and returns at a declared exit. The row is scoped
to its incoming packet and the two locally bound replies. -/
structure Shape (source : FiniteCFG F 1 exits captures) where
  seed : Tm F
  first : F
  second : F
  arg₁ : LetCase.LocallyNameless.Tm Empty F 1
  arg₂ : LetCase.LocallyNameless.Tm Empty F 2
  result : LetCase.LocallyNameless.Tm Empty F 3
  exit : Fin exits
  entry_eq : source.entry.erase = .br 0 seed
  row_eq : (source.block 0).erase = .let₁ (.op first (erase arg₁))
    (.let₁ (.op second (erase arg₂)) (.br (1 + exit.val) (erase result)))

/-- Inspect the actual erased readback, rejecting ambient reads in either
request or the return. The ordinary public constructor checks that the
unchanged entry is a structural jump. -/
def read (source : FiniteCFG F 1 exits captures) : Option (Shape source) :=
  match entry : source.entry.erase, row : (source.block 0).erase with
  | .br 0 seed, .let₁ (.op first a) (.let₁ (.op second b) (.br (exit + 1) result)) => do
    if h : exit < exits then
      let arg₁ ← scopedTerm 1 a
      let arg₂ ← scopedTerm 2 b
      let out ← scopedTerm 3 result
      return ⟨seed, first, second, arg₁.val, arg₂.val, out.val, ⟨exit, h⟩, entry, by
        simpa only [Nat.add_comm 1 exit, arg₁.property, arg₂.property, out.property] using row⟩
    else none
  | _, _ => none

variable {source : FiniteCFG F 1 exits captures}

/-- Carry the entire incoming packet and the first primitive reply. -/
def firstRow (s : Shape source) : Region F :=
  .let₁ (.op s.first (erase s.arg₁)) (.br 1 (.pair (.var 1) (.var 0)))

/-- Destructuring puts the old packet and reply back in their former slots.
The ordered exit has the same external index after inserting the block. -/
def secondRow (s : Shape source) : Region F :=
  .let₂ (.var 0) (.let₁ (.op s.second (erase s.arg₂)) (.br (2 + s.exit.val) (erase s.result)))

structure Emitted (s : Shape source) where
  code : FiniteCFG F 2 exits captures
  entry_eq : code.entry.erase = source.entry.erase
  first_eq : (code.block 0).erase = firstRow s
  second_eq : (code.block 1).erase = secondRow s

def emit (s : Shape source) : Option (Emitted s) := do
  let entry ← scopedRow (2 + exits) captures source.entry.erase
  let first ← scopedRow (2 + exits) (captures + 1) (firstRow s)
  let continuation ← scopedRow (2 + exits) (captures + 1) (secondRow s)
  let code : FiniteCFG F 2 exits captures := ⟨entry.val, fun i => if i.val = 0 then first.val else continuation.val⟩
  return ⟨code,
    entry.property, by simpa [code] using first.property, by simpa [code] using continuation.property⟩

/-- The original packet type stays at block zero. Only the fresh row has a
new packet type pairing it with the first reply. -/
def packets (signature : PrimitiveSignature F) (packet : PacketType) (s : Shape source) :
    Fin 2 → PacketType :=
  fun i => if i.val = 0 then packet else .product packet (signature.reply s.first)

structure Checked (signature : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packet : PacketType) (external : Fin exits → PacketType)
    (source : FiniteCFG F 1 exits captures) where
  shape : Shape source
  emitted : Emitted shape
  sourceTyped : letI := signature.typing; source.HasType context (fun _ => packet) external
  splitTyped : letI := signature.typing;
    emitted.code.HasType context (packets signature packet shape) external

/-- Check both exact profiles. The fresh continuation is ordinary flat
code and can be passed to the existing public readback constructor. -/
def check (signature : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packet : PacketType) (external : Fin exits → PacketType)
    (source : FiniteCFG F 1 exits captures) : Option (Checked signature context packet external source) :=
  letI := signature.typing;
  if old : NamedFlat.check source context (fun _ => packet) external = true then do
    let shape ← read source
    let result ← emit shape
    if accepted : NamedFlat.check result.code context (packets signature packet shape) external = true then do
      return ⟨shape, result, NamedFlat.check_sound _ _ _ _ old, NamedFlat.check_sound _ _ _ _ accepted⟩
    else none
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests
