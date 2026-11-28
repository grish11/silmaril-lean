module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Outer.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms

/-! # Apply checked outer restriction before comparing original witnesses -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgOuterAdmission

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {Φ : Type v} [HasTy Φ (Ty Empty)] {a k n : Nat}
  {outerKeep : Fin 1 ↪ Fin (a + 1)} {innerKeep : Fin (k + 1) ↪ Fin (n + 1)}
  {P : Fin (k + 1) → Ty Empty} {r : Region Φ} {L : LCtx (Ty Empty)}

theorem checked {c : CfgRestriction Φ (a + 1)} (ok : Outer.check? outerKeep innerKeep P r L = some c) :
    c.Valid outerKeep L.length r ∧ compare? innerKeep P (c.retained outerKeep) L = .certified := by
  simp only [Outer.check?, Option.bind_eq_some_iff] at ok
  obtain ⟨compact, lifted, ok⟩ := ok
  split at ok <;> try contradiction
  rename_i certified
  cases Option.some.inj ok
  exact ⟨CfgRestriction.check?_sound lifted, certified⟩

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

theorem compare (roll : IterationRolling C)
    (ok : Outer.compare? outerKeep innerKeep P r L = .certified)
    {h h' : r.HasType [] L} {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  cases found : Outer.check? outerKeep innerKeep P r L with
  | none => simp [Outer.compare?, found] at ok
  | some c =>
      obtain ⟨valid, certified⟩ := checked found
      have retained {t : r.HasType [] L} {b : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
          (original : RegionDenotes J M t b) :
          ∃ ht : (c.retained outerKeep).HasType [] L, RegionDenotes J M ht b := by
        obtain ⟨S, _, w⟩ := valid.readback J M roll original
        have ⟨entry, rows, _⟩ := w
        exact ⟨.cfg (fun i => S (outerKeep i)) entry rows, w.denotes J M⟩
      obtain ⟨_, dl⟩ := retained left
      obtain ⟨_, dr⟩ := retained right
      exact compare?_sound J M roll certified dl dr

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgOuterAdmission
