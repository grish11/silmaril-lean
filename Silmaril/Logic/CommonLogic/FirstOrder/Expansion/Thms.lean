module

public import Silmaril.Logic.CommonLogic.FirstOrder.Expansion.Defs
import Silmaril.Proofs.Logic.CommonLogic.FirstOrderExpansion

@[expose] public section

namespace Silmaril.Logic.CommonLogic.FirstOrder

open Silmaril.Logic.CommonLogic
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

/-- Exact object expansion, not just an isomorphism of underlying carriers. -/
theorem decode_expand {S : Signature} (M : FOL.Structure (publicSignature S))
    (d : M.carrier ()) : decode (expand M d) = M :=
  Silmaril.Proofs.Logic.CommonLogic.FirstOrderExpansion.decode_expand M d

/-- Nonemptiness is the exact object-level boundary for expansion into full CL. -/
theorem exists_expansion_iff {S : Signature} (M : FOL.Structure (publicSignature S)) :
    (∃ N : Core.Model (clSignature S), decode N = M) ↔
      Nonempty (M.carrier ()) := by
  constructor
  · rintro ⟨N, rfl⟩
    exact N.nonempty
  · rintro ⟨d⟩
    exact ⟨expand M d, decode_expand M d⟩

/-- Every nonempty actual public FOL model is exactly a reduct of a CL model. -/
theorem nonempty_modelExpansive : nonemptyComorphism.ModelExpansive := by
  intro S M
  obtain ⟨d⟩ := M.property
  refine ⟨expand M.obj d, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  exact decode_expand M.obj d

theorem nonempty_entails_iff (S : Signature) (Γ : Set (FOL.Sentence (publicSignature S)))
    (p : FOL.Sentence (publicSignature S)) :
    (nonemptyRoom S).Entails Γ p ↔
      (Core.room (clSignature S)).Entails (sentence '' Γ) (sentence p) :=
  nonemptyComorphism.entails_iff nonempty_modelExpansive S Γ p

/-- Theory satisfiability is reflected and preserved for the nonempty source model convention. -/
theorem nonempty_satisfiable_iff (S : Signature) (Γ : Set (FOL.Sentence (publicSignature S))) :
    (∃ M : NonemptyModel S, ∀ p ∈ Γ, p.Holds M.obj) ↔
      ∃ N : Core.Model (clSignature S),
        ∀ q ∈ sentence '' Γ, (Core.room (clSignature S)).Sat N q := by
  constructor
  · rintro ⟨M,hM⟩
    obtain ⟨d⟩ := M.property
    refine ⟨expand M.obj d, ?_⟩
    rintro _ ⟨p,hp,rfl⟩
    apply (sentence_holds _ p).mp
    rw [decode_expand]
    exact hM p hp
  · rintro ⟨N,hN⟩
    exact ⟨⟨decode N,N.nonempty⟩, fun p hp =>
      (sentence_holds N p).mpr (hN (sentence p) ⟨p,hp,rfl⟩)⟩

theorem nonempty_unsatisfiable_iff (S : Signature) (Γ : Set (FOL.Sentence (publicSignature S))) :
    (¬ ∃ M : NonemptyModel S, ∀ p ∈ Γ, p.Holds M.obj) ↔
      ¬ ∃ N : Core.Model (clSignature S),
        ∀ q ∈ sentence '' Γ, (Core.room (clSignature S)).Sat N q :=
  not_congr (nonempty_satisfiable_iff S Γ)

end Silmaril.Logic.CommonLogic.FirstOrder
