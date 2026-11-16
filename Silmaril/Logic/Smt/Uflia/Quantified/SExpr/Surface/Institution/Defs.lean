module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution
open Silmaril.Logic.Smt.Uflia.SExpr

/-- Actual admitted expression bytes under a separately supplied environment,
with independent source truth. Environment arrows are equalities only; whole-script
declarations and capture-safe arbitrary symbol maps are separate work. -/
def plain : Plain (Disc Environment) where
  Sen E := SExpr.ByteAccepted E
  map σ a := σ.down ▸ a
  map_id _ _ := rfl
  map_comp σ τ a := by
    rcases σ with ⟨h⟩; cases h
    rcases τ with ⟨h⟩; cases h
    rfl
  Mod E := Model E.signature
  reduct σ M := σ.down.symm ▸ M
  reduct_id _ _ := rfl
  reduct_comp σ τ M := by
    rcases σ with ⟨h⟩; cases h
    rcases τ with ⟨h⟩; cases h
    rfl
  Sat M a := Holds _ M a.expression
  sat_map σ M a := by
    rcases σ with ⟨h⟩; cases h
    rfl

abbrev institution := plain.toInst
abbrev room (E : Environment) := plain.room E

/-- Decoder comparison into the existing genuinely quantified typed institution. -/
def decodeCorridor (E : Environment) : room E ⟶ Quantified.room E.signature :=
  ⟨(fun a => a.sentence), Disc.functor id, fun M a => (accepted_holds_iff M a).symm⟩

theorem decodeCorridor_modelExpansive (E : Environment) :
    (decodeCorridor E).ModelExpansive := fun M => ⟨M, rfl⟩

def decodeComorphism : Comorphism institution (Quantified.institution String) :=
  Comorphism.ofPlain Uflia.SExpr.signatureFunctor (fun _ a => a.sentence) (fun _ => id)
    (fun _ M a => (accepted_holds_iff M a).symm)
    (fun σ a => by
      rcases σ with ⟨h⟩; cases h
      exact (Quantified.Term.map_id a.sentence).symm)
    (fun σ M => by
      rcases σ with ⟨h⟩; cases h
      exact (Model.reduct_id M).symm)

/-- A source SAT/UNSAT claim retains actual reader and decoder acceptance. -/
def Sat (E : Environment) (bytes : List UInt8) : Prop :=
  ∃ a : SExpr.ByteAccepted E, a.bytes = bytes ∧ ∃ M : Model E.signature, Holds E M a.expression

def Unsat (E : Environment) (bytes : List UInt8) : Prop :=
  ∃ a : SExpr.ByteAccepted E, a.bytes = bytes ∧ ¬ ∃ M : Model E.signature, Holds E M a.expression

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
