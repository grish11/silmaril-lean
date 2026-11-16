module

public import Silmaril.Logic.Egglog.Core.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

namespace Prolog

/-- Ordinary definite programs use total constructor terms and relations, without custom tables. -/
abbrev signature (S : FOL.Signature) : Signature := { S with Function := fun _ _ _ => PEmpty }

def signatures : FOL.Signature ⥤ Signature where
  obj := signature
  map f := { sorts := f.sorts, ops := f.ops, rels := f.rels, functions := fun t => t.elim }
  map_id S := by
    congr 1
    funext n w s t
    exact t.elim
  map_comp f g := by
    congr 1
    funext n w s t
    exact t.elim

def models (S : FOL.Signature) : Model (signature S) ⥤ FOL.Structure S where
  obj M := M.toFOL
  map h := ⟨h.map,h.map_op,h.map_rel⟩

def atom {S : FOL.Signature} {n : Nat} {Γ : Fin n → S.S} (a : Silmaril.Logic.Prolog.Definite.Atom S Γ) :
    Atom (signature S) Γ := .relation a.predicate a.arguments

def sentence {S : FOL.Signature} : Silmaril.Logic.Prolog.Definite.Sentence S → Sentence (signature S)
  | .clause c => .rule ⟨c.scope,c.context,c.body.map atom,atom c.head⟩
  | .query q => .query ⟨q.scope,q.context,q.goals.map atom⟩

private theorem atoms_holds {S : FOL.Signature} {n : Nat} {Γ : Fin n → S.S}
    (M : Model (signature S)) (ρ : ∀ i, M.carrier (Γ i))
    (atoms : List (Silmaril.Logic.Prolog.Definite.Atom S Γ)) :
    (∀ a ∈ atoms.map atom, a.Holds M ρ) ↔ (∀ a ∈ atoms, a.Holds M.toFOL ρ) := by
  constructor
  · intro h a ha
    exact h _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  · intro h a ha
    obtain ⟨original, ho, heq⟩ := List.mem_map.mp ha
    subst a
    exact h original ho

theorem holds {S : FOL.Signature} (M : Model (signature S)) (s : Silmaril.Logic.Prolog.Definite.Sentence S) :
    (sentence s).Holds M ↔ s.Holds M.toFOL := by
  cases s with
  | clause c =>
    apply forall_congr'
    intro ρ
    exact imp_congr (atoms_holds M ρ c.body) Iff.rfl
  | query q =>
    apply exists_congr
    intro ρ
    exact atoms_holds M ρ q.goals

theorem sentence_map {S T : FOL.Signature} (f : S ⟶ T) (s : Silmaril.Logic.Prolog.Definite.Sentence S) :
    sentence (s.map f) = (sentence s).map (signatures.map f) := by
  cases s <;> simp [sentence, Silmaril.Logic.Prolog.Definite.Sentence.map,
    Sentence.map, Silmaril.Logic.Prolog.Definite.Clause.map, Silmaril.Logic.Prolog.Definite.Query.map,
    Rule.map, Query.map, List.map_map, atom, Silmaril.Logic.Prolog.Definite.Atom.map,
    Atom.map, signatures, signature, Function.comp_def]

def expansion {S : FOL.Signature} (M : FOL.Structure S) : Model (signature S) where
  toFOL := M
  row f := f.elim
  functional f := f.elim

end Prolog

/-- A genuine model-expansive comorphism, including existential queries, from definite Prolog
into the constructor/relation fragment of the partial-table institution. -/
def fromProlog : Inst.CoHom Silmaril.Logic.Prolog.Definite.inst inst where
  Φ := Prolog.signatures
  ρ :=
    { app := fun S => ⟨Prolog.sentence, Prolog.models S, Prolog.holds⟩
      naturality := by intro S T f; exact Room.hom_ext (funext (Prolog.sentence_map f)) rfl }

theorem fromProlog_modelExpansive : fromProlog.ModelExpansive :=
  fun _ M => ⟨Prolog.expansion M,rfl⟩

end Silmaril.Logic.Egglog.Core
