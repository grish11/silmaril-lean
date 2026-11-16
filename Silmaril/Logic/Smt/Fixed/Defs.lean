module

public import Silmaril.Logic.Smt.Defs
public import Silmaril.Logic.Inst.Builders.Core.Defs

/-!
# SMT problems over fixed declarations

Declarations live in the signature; sentences are lists of assertions. Models carry
evidence that every declared constant has the required sort. Signatures and models use
discrete categories: symbol renamings remain a separate extension. These definitions use
the existing evaluator's documented fragment and division-by-zero convention, and do not
claim the QF-UFLIA fragment or enforce `set-logic`.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Fixed

open CategoryTheory Silmaril.Inst

abbrev Signature := List (String × Ty)
abbrev Sentence := List Term

/-- A well-sorted assignment for the fixed declarations. Inconsistent duplicate
declarations may give an empty model class; no well-formedness is assumed silently. -/
def Assignment (Γ : Signature) :=
  { ρ : Model // (Γ.all fun d => (ρ d.1).hasSort d.2) = true }

def Holds {Γ : Signature} (ρ : Assignment Γ) (φ : Sentence) : Prop :=
  (φ.all fun t => t.eval Γ ρ.val == some (.bool true)) = true

/-- Move fixed declarations into the sentence of the whole-script presentation. -/
def package (Γ : Signature) (φ : Sentence) : Script :=
  ⟨Γ.map (fun d => Cmd.declare d.1 d.2) ++ φ.map Cmd.assert⟩

def Sat (Γ : Signature) (φ : Sentence) : Prop := ∃ ρ : Assignment Γ, Holds ρ φ

/-- The institution over discrete declaration signatures. Its identity-only signature
maps transport the proof carried by an assignment. -/
def plain : Plain (Disc Signature) where
  Sen _ := Sentence
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod Γ := Assignment Γ
  reduct σ ρ := σ.down.symm ▸ ρ
  reduct_id _ _ := rfl
  reduct_comp σ τ ρ := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Sat := Holds
  sat_map σ ρ φ := by
    rcases σ with ⟨h⟩
    cases h
    rfl

abbrev institution := plain.toInst
abbrev room (Γ : Signature) := plain.room Γ

end Silmaril.Logic.Smt.Fixed
