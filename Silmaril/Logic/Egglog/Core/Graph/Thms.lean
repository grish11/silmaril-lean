module

public import Silmaril.Logic.Egglog.Core.Graph.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Graph

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem atom_map {S T : Signature} (f : S ⟶ T) {n : Nat} {Γ : Fin n → S.S}
    (a : Atom S Γ) : atom (a.map f) = (atom a).map (signatureMap f) := by
  cases a with
  | equal e => rfl
  | relation r args => rfl
  | row t args value =>
    simp only [Atom.map, atom, FOL.Formula.map, signatureMap]
    congr 1
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
    · congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    · apply Function.hfunext rfl
      intro i j hij
      cases hij
      exact Fin.cases HEq.rfl (fun _ => HEq.rfl) i

theorem conjunction_map {S T : Signature} (f : S ⟶ T) {n : Nat} {Γ : Fin n → S.S}
    (as : List (Atom S Γ)) :
    conjunction (as.map (Atom.map f)) = (conjunction as).map (signatureMap f) := by
  induction as with
  | nil => rfl
  | cons a rest ih => exact congrArg₂ FOL.Formula.and (atom_map f a) ih

theorem sentence_map {S T : Signature} (f : S ⟶ T) (s : Sentence S) :
    sentence (s.map f) = (sentence s).map (signatureMap f) := by
  cases s with
  | rule r =>
    dsimp only [Sentence.map, Rule.map, sentence]
    rw [EQtoFOL.map_closeAll]
    apply congrArg (EQtoFOL.closeAll (Sg := signature T) (f.sorts ∘ r.context))
    rw [conjunction_map, atom_map]
    rfl
  | query q =>
    have h := EQtoFOL.map_closeAll (signatureMap f) q.context (.not (conjunction q.goals))
    dsimp only [Sentence.map, Query.map, sentence]
    rw [conjunction_map]
    exact congrArg (fun s : FOL.Sentence (signature T) =>
      (⟨s.ctx, .not s.formula⟩ : FOL.Sentence (signature T))) h.symm

/-- The normalized rule/query language embeds into its full first-order graph
institution. Both endpoints retain the same functional partial-table models. -/
def fromCore : Inst.CoHom Core.inst inst where
  Φ := 𝟭 Signature
  ρ :=
    { app := corridor
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (sentence_map f)) rfl }

theorem fromCore_modelExpansive : fromCore.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem theory_holds_iff {S : Signature} (M : Model S) (H : Set (Sentence S)) :
    (∀ s ∈ H, s.Holds M) ↔ ∀ p ∈ sentence '' H, p.Holds (model M) := by
  constructor
  · rintro h p ⟨s, hs, rfl⟩
    exact (sentence_holds M s).mpr (h s hs)
  · intro h s hs
    exact (sentence_holds M s).mp (h _ ⟨s, hs, rfl⟩)

theorem sat_iff {S : Signature} (H : Set (Sentence S)) :
    (∃ M : Model S, ∀ s ∈ H, s.Holds M) ↔
      ∃ M : Model S, ∀ p ∈ sentence '' H, p.Holds (model M) :=
  exists_congr (fun M => theory_holds_iff M H)

theorem unsat_iff {S : Signature} (H : Set (Sentence S)) :
    (¬ ∃ M : Model S, ∀ s ∈ H, s.Holds M) ↔
      ¬ ∃ M : Model S, ∀ p ∈ sentence '' H, p.Holds (model M) :=
  not_congr (sat_iff H)

end Silmaril.Logic.Egglog.Core.Graph
