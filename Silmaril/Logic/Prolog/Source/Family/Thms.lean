module

public import Silmaril.Logic.Prolog.Source.Family.Defs

@[expose] public section
namespace Silmaril.Logic.Prolog.Source.Families
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

theorem toDefinite_modelExpansive : toDefinite.ModelExpansive := fun _ M => ⟨M, rfl⟩
theorem toFirstOrder_modelExpansive : toFirstOrder.ModelExpansive := fun _ M => ⟨M, rfl⟩
theorem package_modelExpansive (V : Vocabulary) : (package V).ModelExpansive :=
  fun M => ⟨M, rfl⟩

def TheoryHolds {V : Vocabulary} (M : FOL.Structure V.signature) (H : Set (Family V)) :
    Prop := ∀ s ∈ H, s.Holds M

def Sat {V : Vocabulary} (H : Set (Family V)) : Prop := ∃ M, TheoryHolds M H
def Unsat {V : Vocabulary} (H : Set (Family V)) : Prop := ¬ Sat H

theorem theory_holds_iff_definite {V : Vocabulary} (M : FOL.Structure V.signature)
    (H : Set (Family V)) :
    TheoryHolds M H ↔ Definite.TheoryHolds M (Family.encode '' H) := by
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    exact (s.encode_holds M).mpr (h s hs)
  · intro h s hs
    exact (s.encode_holds M).mp (h _ ⟨s, hs, rfl⟩)

theorem sat_iff_definite {V : Vocabulary} (H : Set (Family V)) :
    Sat H ↔ Definite.Sat (Family.encode '' H) :=
  exists_congr fun M => theory_holds_iff_definite M H

theorem unsat_iff_definite {V : Vocabulary} (H : Set (Family V)) :
    Unsat H ↔ Definite.Unsat (Family.encode '' H) := not_congr (sat_iff_definite H)

theorem entails_iff_definite (V : Vocabulary) (H : Set (Family V)) (s : Family V) :
    (room V).Entails H s ↔
      (Definite.room V.signature).Entails (Family.encode '' H) s.encode :=
  toDefinite.entails_iff toDefinite_modelExpansive V H s

def firstOrder {V : Vocabulary} (s : Family V) : FOL.Sentence V.signature :=
  s.encode.encode

theorem firstOrder_holds {V : Vocabulary} (M : FOL.Structure V.signature) (s : Family V) :
    (firstOrder s).Holds M ↔ s.Holds M :=
  s.encode.encode_holds M |>.trans (s.encode_holds M)

theorem sat_iff_firstOrder {V : Vocabulary} (H : Set (Family V)) :
    Sat H ↔ ∃ M : FOL.Structure V.signature, ∀ φ ∈ firstOrder '' H, φ.Holds M := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨M, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact (firstOrder_holds M s).mpr (h s hs)
  · rintro ⟨M, h⟩
    exact ⟨M, fun s hs => (firstOrder_holds M s).mp (h _ ⟨s, hs, rfl⟩)⟩

theorem unsat_iff_firstOrder {V : Vocabulary} (H : Set (Family V)) :
    Unsat H ↔ ¬ ∃ M : FOL.Structure V.signature, ∀ φ ∈ firstOrder '' H, φ.Holds M :=
  not_congr (sat_iff_firstOrder H)

theorem entails_iff_firstOrder (V : Vocabulary) (H : Set (Family V)) (s : Family V) :
    (room V).Entails H s ↔
      (FOL.room V.signature).Entails (firstOrder '' H) (firstOrder s) :=
  toFirstOrder.entails_iff toFirstOrder_modelExpansive V H s

/-- The satisfaction condition acts on arbitrary sets under an actual symbol map. -/
theorem theory_holds_map {V W : Vocabulary} (f : V ⟶ W)
    (M : FOL.Structure W.signature) (H : Set (Family V)) :
    TheoryHolds M (Family.map f '' H) ↔
      TheoryHolds ((FOL.Structure.reduct f).obj M) H := by
  constructor
  · intro h s hs
    exact (Family.holds_map f M s).mp (h _ ⟨s, hs, rfl⟩)
  · rintro h _ ⟨s, hs, rfl⟩
    exact (Family.holds_map f M s).mpr (h s hs)

theorem entails_map {V W : Vocabulary} (f : V ⟶ W) (H : Set (Family V))
    (s : Family V) (h : (room V).Entails H s) :
    (room W).Entails (Family.map f '' H) (s.map f) := (corridor f).entails_map h

/-- Reflection across a symbol map needs real model coverage; it is not
inferred from the existence of its sentence map. -/
theorem entails_map_iff {V W : Vocabulary} (f : V ⟶ W)
    (hf : (corridor f).ModelExpansive) (H : Set (Family V)) (s : Family V) :
    (room V).Entails H s ↔ (room W).Entails (Family.map f '' H) (s.map f) :=
  (corridor f).entails_map_iff hf H s

/-- This remains a positive fragment, even for infinite sets of local sentences. -/
theorem sat_every_theory {V : Vocabulary} (H : Set (Family V)) : Sat H :=
  (sat_iff_definite H).mpr (Definite.sat_every_theory _)

end Silmaril.Logic.Prolog.Source.Families
