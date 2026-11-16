module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete.Defs
public import Silmaril.Logic.Smt.SExpr.Reader.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
variable {E : Environment}

@[simp] theorem Sentence.decode_mk (a : Accepted E) : (Sentence.mk a).decode = a.formula := rfl

theorem Sentence.sound {a b : Accepted E} (h : a.formula = b.formula) :
    Sentence.mk a = Sentence.mk b := Quotient.sound h

/-- The quotient identifies precisely decoded formula equality, including both
directions for arbitrary quotient sentences. -/
theorem Sentence.decode_eq_iff (s t : Sentence E) : s.decode = t.decode ↔ s = t := by
  refine Quotient.inductionOn₂ s t ?_
  intro a b
  exact ⟨fun h => Quotient.sound h, fun h => congrArg Sentence.decode h⟩

theorem Sentence.mk_eq_mk_iff (a b : Accepted E) :
    Sentence.mk a = Sentence.mk b ↔ a.formula = b.formula :=
  (Sentence.decode_eq_iff (Sentence.mk a) (Sentence.mk b)).symm

@[simp] theorem holds_mk (M : Uflia.Model E.signature) (a : Accepted E) :
    Holds M (Sentence.mk a) ↔ M.Holds a.formula := Iff.rfl

/-- Source syntax legality follows from its actual byte-reader witness. -/
theorem Accepted.legal (a : Accepted E) : Smt.SExpr.Writer.LegalExpr a.expression :=
  Smt.SExpr.Writer.readForms_legal a.bytes [a.expression] a.read a.expression (by simp)

/-- Decoder satisfaction of the concrete bytes is exactly that of the quotient
representative's computed formula in the same model. -/
theorem Accepted.byteHolds_iff (a : Accepted E) (M : Uflia.Model E.signature) :
    ByteHolds E a.bytes M ↔ M.Holds a.formula := by
  constructor
  · rintro ⟨e, φ, hread, hdecode, hholds⟩
    have hexpr : a.expression = e := List.singleton_inj.mp (Option.some.inj (a.read.symm.trans hread))
    subst e
    have hformula : a.formula = φ := Option.some.inj (a.decoded.symm.trans hdecode)
    exact hformula ▸ hholds
  · intro hholds
    exact ⟨a.expression, a.formula, a.read, a.decoded, hholds⟩

theorem holds_mk_iff_byteHolds (M : Uflia.Model E.signature) (a : Accepted E) :
    Holds M (Sentence.mk a) ↔ ByteHolds E a.bytes M :=
  (a.byteHolds_iff M).symm

/-- Equal concrete bytes cannot produce different quotient sentences. -/
theorem same_bytes_same_sentence (a b : Accepted E) (hbytes : a.bytes = b.bytes) :
    Sentence.mk a = Sentence.mk b := by
  have hr : some [a.expression] = some [b.expression] := by
    rw [← a.read, ← b.read, hbytes]
  have he : a.expression = b.expression := List.singleton_inj.mp (Option.some.inj hr)
  apply Sentence.sound
  exact Option.some.inj (a.decoded.symm.trans (he ▸ b.decoded))

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
