module

public import Silmaril.SSA.Isotope.LetPar.Native.Defs

/-! # Ordered effect traces for LetPar -/

@[expose] public section

namespace Silmaril.Isotope.LetPar.EffectTrace

universe v w r

/-- A sequential trace records its instruction order. The unknown trace abstracts
parallel computations where both branches have effects. -/
abbrev Trace (Φ : Type v) := Option (List Φ)

variable {ν : Type w} {Φ : Type v} {ε : Type r}

/-- The trace of a term with no recorded instruction effects. -/
abbrev empty : Trace Φ := some []

/-- Append known traces in order. An unknown trace gives an unknown result. -/
def seq : Trace Φ → Trace Φ → Trace Φ
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- Retain a branch trace when the other is empty. The result is unknown when
neither branch is known to have an empty trace. -/
def par : Trace Φ → Trace Φ → Trace Φ
  | some [], b => b
  | a, some [] => a
  | _, _ => none

variable [HasEff Φ ε] [DecidableEq ε] (pureEff : ε)

/-- Record a single opcode unless the signature classifies it as pure. -/
def instruction (f : Φ) : Trace Φ :=
  if (instrEff f : ε) = pureEff then empty else some [f]

/-- Record effectful opcodes in evaluation order, ignoring binder values.
Parallel pairing retains a single nonempty trace in either branch. -/
def observe : {n : Nat} → Tm ν Φ n → Trace Φ
  | _, .fv _ => empty
  | _, .bv _ => empty
  | _, .op f a => seq (observe a) (instruction pureEff f)
  | _, .let₁ a b => seq (observe a) (observe b)
  | _, .unit => empty
  | _, .pair a b => seq (observe a) (observe b)
  | _, .let₂ a b => seq (observe a) (observe b)
  | _, .par a b => par (observe a) (observe b)
  | _, .inl h _ | _, .inr h _ | _, .case h _ _ _ | _, .abort h _ => False.elim (h rfl)
  | _, .iter h _ _ => nomatch h

/-- A native straight-line program that supplies unit to each instruction and discards its
result. The program returns unit after the sequence. -/
def word {n : Nat} : List Φ → LetSeq.LocallyNameless.Tm ν Φ n
  | [] => .unit
  | f :: fs => .let₁ (.op f .unit) (word fs)

namespace Singleton

/-! Scoped instances for the single object type and the corresponding opcode signature. -/

scoped instance : HasProduct Unit := ⟨fun _ _ => ()⟩
scoped instance : HasUnit Unit := ⟨()⟩
scoped instance {Φ : Type v} : HasTy Φ Unit := ⟨fun _ => (), fun _ => ()⟩

end Singleton

end Silmaril.Isotope.LetPar.EffectTrace
