module

public import Silmaril.Logic.CommonLogic.ManySorted.Expansion.Defs
public import Silmaril.Logic.Institution.Faithful
public import Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion

/-! Decoder recovery up to structure isomorphism and satisfaction transport.
The single-signature corridor asserts neither literal object-surjectivity nor a general institution comorphism. -/
@[expose] public section
noncomputable section

namespace Silmaril.Logic.CommonLogic.ManySorted.Expansion

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic Silmaril.Logic.CommonLogic.ManySorted

variable {S : FOL.Signature}

/-- An actual FOL structure isomorphism, with possibly empty source carriers. -/
def decodeExpandIso (M : FOL.Structure S) : decode (expand M) ≅ M :=
  Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.decodeExpandIso M

theorem decoded_coverage (M : FOL.Structure S) :
    ∃ N : TypedModel S, Nonempty (decode N ≅ M) :=
  ⟨expand M, ⟨decodeExpandIso M⟩⟩

theorem expanded_satisfaction (M : FOL.Structure S) (p : FOL.Sentence S) :
    (sentence p).Holds (expand M).obj Fin.elim0 Fin.elim0 ↔ p.Holds M :=
  (sentence_holds (expand M) p).symm.trans
    (Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.sentence_holds_iso (decodeExpandIso M) p)

/-- A single-signature CL room retaining every arrow between operation-typed models. -/
def typedRoom (S : FOL.Signature) : Room.{0, 0, 1} :=
  ⟨Core.Sentence (signature S), Cat.of (TypedModel S),
    fun M p => p.Holds M.obj Fin.elim0 Fin.elim0⟩

/-- This corridor is not yet bundled across signatures into an institution map. -/
def comparison (S : FOL.Signature) : FOL.room S ⟶ typedRoom S :=
  ⟨sentence, models S, fun M p => (sentence_holds M p).symm⟩

theorem source_isoInvariant (S : FOL.Signature) : (FOL.room S).IsoInvariant := by
  intro M N h p
  obtain ⟨e⟩ := h
  exact Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion.sentence_holds_iso e p

theorem isoExpansive (S : FOL.Signature) : (comparison S).IsoExpansive :=
  fun M => ⟨expand M, ⟨decodeExpandIso M⟩⟩

/-- The existing weaker-than-equality borrowing interface, derived through isomorphism. -/
theorem elemExpansive (S : FOL.Signature) : (comparison S).ElemExpansive :=
  Corridor.IsoExpansive.elemExpansive (source_isoInvariant S) (isoExpansive S)

theorem entails_iff (S : FOL.Signature) (Γ : Set (FOL.Sentence S)) (p : FOL.Sentence S) :
    (FOL.room S).Entails Γ p ↔ (typedRoom S).Entails (sentence '' Γ) (sentence p) :=
  Corridor.entails_map_iff_of_elemExpansive (elemExpansive S) Γ p

theorem satisfiable_iff (S : FOL.Signature) (Γ : Set (FOL.Sentence S)) :
    (∃ M : FOL.Structure S, ∀ p ∈ Γ, p.Holds M) ↔
      ∃ N : TypedModel S, ∀ q ∈ sentence '' Γ,
        q.Holds N.obj Fin.elim0 Fin.elim0 := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨expand M, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (expanded_satisfaction M p).mpr (hM p hp)
  · rintro ⟨N, hN⟩
    exact ⟨decode N, fun p hp => (sentence_holds N p).mpr
      (hN (sentence p) ⟨p, hp, rfl⟩)⟩

theorem unsatisfiable_iff (S : FOL.Signature) (Γ : Set (FOL.Sentence S)) :
    (¬ ∃ M : FOL.Structure S, ∀ p ∈ Γ, p.Holds M) ↔
      ¬ ∃ N : TypedModel S, ∀ q ∈ sentence '' Γ,
        q.Holds N.obj Fin.elim0 Fin.elim0 :=
  not_congr (satisfiable_iff S Γ)

/-- Raw CL satisfiability includes the generated typing theory explicitly. -/
theorem satisfiable_raw_iff (S : FOL.Signature) (Γ : Set (FOL.Sentence S)) :
    (∃ M : FOL.Structure S, ∀ p ∈ Γ, p.Holds M) ↔
      ∃ N : Core.Model (signature S),
        ∀ q ∈ typingTheory S ∪ sentence '' Γ, q.Holds N Fin.elim0 Fin.elim0 := by
  rw [satisfiable_iff S Γ]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N.obj, ?_⟩
    intro q hq
    rcases hq with ht | hp
    · exact (wellTyped_iff N.obj).mp N.property q ht
    · exact hN q hp
  · rintro ⟨N, hN⟩
    have typed : WellTyped N := (wellTyped_iff N).mpr (fun q hq => hN q (Or.inl hq))
    exact ⟨⟨N, typed⟩, fun q hq => hN q (Or.inr hq)⟩

end Silmaril.Logic.CommonLogic.ManySorted.Expansion
