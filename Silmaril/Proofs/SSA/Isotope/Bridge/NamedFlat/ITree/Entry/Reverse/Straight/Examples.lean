module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Thms

/-! # Checked reversion of lets and a sum case with a back edge -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.Examples

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

private abbrev SortName := ULift.{1} Unit
private abbrev Label := ULift.{1} Nat
private instance : HasTy Empty (Ty SortName) := ⟨Empty.elim, Empty.elim⟩
private instance : HasEff Empty Bool := ⟨Empty.elim⟩
private instance : AtomValues SortName := ⟨fun _ => ULift.{1} Unit⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Empty

private instance : DecidableEq signature.Instr := fun f => Empty.elim f

private abbrev ports : Interface SortName Register Label :=
  numberedInterface .nil [⟨22⟩, ⟨11⟩] (fun _ => .unit)

private def labels (_ : Fin 1) : Label := ⟨5⟩
private def fields (_ : Label) : List (Register × Ty SortName) := [(⟨3⟩, .unit)]

private def flat (loop : Bool) : FiniteCFG signature.Instr 1 ports.exits.length ports.slots where
  entry := .br 0 (.pair .unit .unit)
  block _ := .let₂ (.bv 0) (.let₁ (.bv 0) (if loop then
    .br 0 (.pair (.bv 1) (.bv 0))
    else .br 2 (.pair .unit (.pair (.bv 0) .unit))))

private def R (_ : Fin 1) : Ty SortName := .product .unit .unit

private theorem typed (loop : Bool) : (flat loop).HasType ports.context R
    (LiveOut.exitInterface ports fields).external :=
  NamedFlat.check_sound (flat loop) ports.context R _ (by cases loop <;> decide)

private def lowered (loop : Bool) : Lowered ports fields (flat loop) :=
  (lowerFresh labels ports.context ports.exits ports.external fields (flat loop)).get
    (by cases loop <;> decide)

private theorem saved (loop : Bool) : (lowered loop).SavesCaptures := by
  cases loop <;> decide

private def admitted (loop : Bool) : LiveOut.Admission signature ports fields (lowered loop).source :=
  admit (lowered loop) R (saved loop) (empty_of_no_captures _ rfl (saved loop)) (by cases loop <;> decide)

-- The ordinary executable admission accepts the same generated reversion.
example : ((lowered false).reAdmit R).isSome = true := by decide
example : ((lowered true).reAdmit R).isSome = true := by decide

private abbrev C := AtomValues.carrier (κ := SortName)
private def packet : Value (Sigma C) := encodeValue C (Region.packedInputType ports.context.toList) PUnit.unit

example {E : Type → Type} (M : Model (κ := SortName) E signature.Instr)
    (ambient : Env (Sigma C)) (loop : Bool) :
    region M.raw (extend ambient packet) (Program.ofCFGEntry (typed loop)).code =
      region M.raw (extend ambient packet) (admitted loop).program.code :=
  (lowered loop).packed_roundTrip M (typed loop) (admitted loop) PUnit.unit ambient

private inductive SumOp where
  | seed
  deriving DecidableEq

private def sumType : Ty SortName := .coprod .unit (.product .unit .unit)

private instance : HasTy SumOp (Ty SortName) := ⟨fun _ => .unit, fun _ => sumType⟩
private instance : HasEff SumOp Bool := ⟨fun _ => true⟩

private def sumSignature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := SumOp

private instance : DecidableEq sumSignature.Instr := inferInstanceAs (DecidableEq SumOp)

private def noFields (_ : Label) : List (Register × Ty SortName) := []

-- One arm exits with the left binder. The other keeps the original sum
-- in scope across a differently typed right binder and feeds it back.
private def sumLoop : FiniteCFG sumSignature.Instr 1 ports.exits.length ports.slots where
  entry := .let₁ (.op .seed .unit) (.br 0 (.bv 0))
  block _ := .case (.bv 0) (.br 2 (.pair (.bv 0) .unit)) (.br 0 (.bv 1))

private theorem sumTyped : sumLoop.HasType ports.context (fun _ => sumType)
    (LiveOut.exitInterface ports noFields).external :=
  NamedFlat.check_sound sumLoop ports.context (fun _ => sumType) _ (by decide)

private def sumLowered : Lowered ports noFields sumLoop :=
  (lowerFresh labels ports.context ports.exits ports.external noFields sumLoop).get (by decide)

private def sumAdmitted : LiveOut.Admission sumSignature ports noFields sumLowered.source :=
  admit sumLowered (fun _ => sumType) (by decide) (by decide) (by decide)

example : (sumLowered.reAdmit (fun _ => sumType)).isSome = true := by decide

example {E : Type → Type} (M : Model (κ := SortName) E sumSignature.Instr)
    (ambient : Env (Sigma C)) :
    region M.raw (extend ambient packet) (Program.ofCFGEntry sumTyped).code =
      region M.raw (extend ambient packet) sumAdmitted.program.code :=
  sumLowered.packed_roundTrip M sumTyped sumAdmitted PUnit.unit ambient

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.Examples
