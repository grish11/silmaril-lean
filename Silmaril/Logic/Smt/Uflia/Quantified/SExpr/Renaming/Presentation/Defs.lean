module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface.Institution.Thms
public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Defs

/-! Every actual admitted byte expression remains a source representative.
Bound-name changes need not preserve representative bytes under identity or
composition, so the institution action uses this exact decoded-equality quotient.
Truth is lifted from independent direct source interpretation. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Presentation
open Silmaril.Logic.Smt.Uflia.SExpr

abbrev Representative (E : Environment) := SExpr.ByteAccepted E

def representativeSetoid (E : Environment) : Setoid (Representative E) where
  r a b := a.sentence = b.sentence
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

def Sentence (E : Environment) := Quotient (representativeSetoid E)

def Sentence.mk {E : Environment} (representative : Representative E) : Sentence E :=
  Quotient.mk _ representative

def Sentence.decode {E : Environment} : Sentence E → Quantified.Sentence E.signature :=
  Quotient.lift (fun representative => representative.sentence) (fun _ _ same => same)

/-- Quotient truth retains the direct interpreter. Adequacy proves this truth
independent of which actual byte representative is used. -/
def Holds {E : Environment} (M : Model E.signature) : Sentence E → Prop :=
  Quotient.lift (fun representative => Surface.Holds E M representative.expression) (by
    intro a b same
    apply propext
    rw [Surface.accepted_holds_iff M a, Surface.accepted_holds_iff M b]
    change Quantified.Sentence.Holds a.sentence M ↔ Quantified.Sentence.Holds b.sentence M
    rw [same])

@[simp] theorem holds_mk {E : Environment} (M : Model E.signature) (a : Representative E) :
    Holds M (Sentence.mk a) ↔ Surface.Holds E M a.expression := Iff.rfl

theorem holds_iff_decode {E : Environment} (M : Model E.signature) (sentence : Sentence E) :
    Holds M sentence ↔ Quantified.Sentence.Holds sentence.decode M := by
  induction sentence using Quotient.inductionOn with
  | h a => exact Surface.accepted_holds_iff M a

/-- Every successfully parsed Boolean source expression occurs in the
presentation, retaining its original actual bytes and reader equation. -/
theorem every_parsed_represented {E : Environment} {bytes : List UInt8}
    {sentence : Quantified.Sentence E.signature} (parsed : SExpr.parse? E bytes = some sentence) :
    ∃ a : Representative E, a.bytes = bytes ∧ (Sentence.mk a).decode = sentence :=
  Surface.byteAccepted_of_parsed parsed

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Presentation
