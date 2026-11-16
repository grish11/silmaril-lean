module

public import Silmaril.Logic.CommonLogic.ManySorted.Thms

@[expose] public section

namespace Silmaril.Logic.CommonLogic.ManySorted

open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic

/-- Arbitrarily many source sorts, with no operations or relations requiring inhabitants. -/
def emptySignature (Sorts : Type) : FOL.Signature :=
  ⟨⟨Sorts, fun _ _ _ => Empty⟩, fun _ _ => Empty⟩

/-- CL allows junk and total applications even when every sort predicate is false. -/
def junkModel (S : FOL.Signature) : Core.Model (signature S) where
  Reference := Unit ⊕ Head S
  Discourse := Unit
  nonempty := ⟨()⟩
  embed := Sum.inl
  injective := Sum.inl_injective
  discourse := Empty.elim
  nondiscourse := Sum.inr
  outside _ _ := by intro h; cases h
  sequence := Empty.elim
  function := fun _ _ => ()
  relation := fun _ _ => False

/-- A genuine typed CL model whose discourse is nonempty and every source sort is empty. -/
def emptyModel (Sorts : Type) : TypedModel (emptySignature Sorts) where
  obj := junkModel (emptySignature Sorts)
  property := fun o => Empty.elim o

/-- Junk in the CL discourse never introduces a source inhabitant. -/
theorem decodedEmpty (Sorts : Type) (s : Sorts) :
    IsEmpty ((decode (emptyModel Sorts)).carrier s) :=
  ⟨fun x => x.property⟩

/-- Even an unused quantified variable must retain its empty-sort guard. -/
theorem empty_sort_all {S : FOL.Signature} {n k : Nat}
    (M : Core.Model (signature S)) (s : S.S)
    (p : Core.Formula (signature S) (n+1) k)
    (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (h : ∀ x, ¬ M.relation (M.nondiscourse (.sort s)) [x]) :
    (Core.Formula.all (.impl (guard s (.var 0)) p)).Holds M ρ σ := by
  intro x hx
  exact False.elim (h x hx)

theorem empty_sort_not_exists {S : FOL.Signature} {n k : Nat}
    (M : Core.Model (signature S)) (s : S.S)
    (p : Core.Formula (signature S) (n+1) k)
    (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (h : ∀ x, ¬ M.relation (M.nondiscourse (.sort s)) [x]) :
    ¬ (Core.Formula.ex (.conj (guard s (.var 0)) p)).Holds M ρ σ := by
  rintro ⟨x, hx, _⟩
  exact h x hx

/-- Removing existential guards admits the junk individual of an empty-sort model. -/
theorem unguarded_exists_junk (Sorts : Type) :
    (Core.Formula.ex (.tt : Core.Formula (signature (emptySignature Sorts)) 1 0)).Holds
      (emptyModel Sorts).obj Fin.elim0 Fin.elim0 :=
  ⟨(), True.intro⟩

/-- This signature supplies constants (and operations at every other profile). -/
def constantSignature : FOL.Signature :=
  ⟨⟨Unit, fun _ _ _ => Unit⟩, fun _ _ => Empty⟩

/-- A raw CL model with false output predicates cannot decode a source constant. -/
theorem typing_is_required : ¬ WellTyped (junkModel constantSignature) := by
  intro h
  exact h (n := 0) (w := fun _ => ()) (s := ()) () Fin.elim0 (fun i => Fin.elim0 i)

/-- A nullary operation forces precisely its output sort to be inhabited. -/
theorem constant_inhabited {S : FOL.Signature} {w : Fin 0 → S.S} {s : S.S}
    (M : TypedModel S) (o : S.Op 0 w s) : Nonempty ((decode M).carrier s) :=
  ⟨(decode M).op o (fun i => i.elim0)⟩

/-- Identifying source sorts is allowed: their predicates may coincide after reduct. -/
theorem reduct_carrier_eq {S T : FOL.Signature} (f : S ⟶ T) (M : TypedModel T)
    (s t : S.S) (h : f.sorts s = f.sorts t) :
    (decode ((typedReduct f).obj M)).carrier s =
      (decode ((typedReduct f).obj M)).carrier t := by
  change carrier M.obj (f.sorts s) = carrier M.obj (f.sorts t)
  rw [h]

end Silmaril.Logic.CommonLogic.ManySorted
