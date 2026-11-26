module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (HandledTrace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type} [DecidableEq F]
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

/-- At one supplied store, the Boolean compares the original runners
when both entries produce typed packets. -/
theorem StructuralEntry.refinementFromStore?_eq_some_iff (initial : V → Value Atom) (verdict : Bool) :
    left.refinementFromStore? right initial = some verdict ↔
      (∃ a, left.evalSeed initial = PacketType.encode inputType a) ∧
      (∃ b, right.evalSeed initial = PacketType.encode rightType b) ∧
      (verdict = true ↔
        ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
          ∀ x, policy.initial x → ∀ trace,
            HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source initial) trace →
            HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target initial) trace) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.store_eq_some left right initial verdict

/-- The finite verdict decides directed handled-trace inclusion on the
original RTL runners at every jointly typed initial store. -/
theorem StructuralEntry.refinementOverCaptures_eq_some_iff (verdict : Bool) :
    (left.refinementOverCaptures right).verdict = some verdict ↔
      (verdict = true ↔
        ∀ initial, (∃ a, left.evalSeed initial = PacketType.encode inputType a) →
          (∃ b, right.evalSeed initial = PacketType.encode rightType b) →
          ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
            ∀ x, policy.initial x → ∀ trace,
              HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source initial) trace →
              HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target initial) trace) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.domain_eq_some left right verdict

/-- Every generated representative supplies two typed seeds. -/
theorem StructuralEntry.refinementOverCaptures_hasVerdict :
    (left.refinementOverCaptures right).verdict.isSome = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.domain_has_verdict left right

/-- Every negative verdict comes from a failure at an actual representative. -/
theorem StructuralEntry.refinementOverCaptures_eq_false_iff :
    (left.refinementOverCaptures right).verdict = some false ↔
      ∃ initial ∈ left.jointStores right, left.refinementFromStore? right initial = some false :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.domain_eq_false left right

theorem StructuralEntry.refinementOverCaptures_emptyDomain_iff :
    (left.refinementOverCaptures right).emptyDomain = true ↔ ¬ ∃ initial,
      (∃ a, left.evalSeed initial = PacketType.encode inputType a) ∧
        (∃ b, right.evalSeed initial = PacketType.encode rightType b) :=
  List.isEmpty_iff.trans (left.jointStores_eq_nil_iff right)

theorem StructuralEntry.refinementOverCaptures_vacuous
    (empty : (left.refinementOverCaptures right).emptyDomain = true) :
    (left.refinementOverCaptures right).verdict = some true := by
  have noneTyped := (left.refinementOverCaptures_emptyDomain_iff right).mp empty
  exact (left.refinementOverCaptures_eq_some_iff right true).mpr
    ⟨fun _ initial typedLeft typedRight => (noneTyped ⟨initial, typedLeft, typedRight⟩).elim, fun _ => rfl⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
