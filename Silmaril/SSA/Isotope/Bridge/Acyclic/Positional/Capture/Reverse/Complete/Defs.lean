module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms

/-! # Checked positional realization of a packed LetCase result -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

open Region (packedExitType)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {n : Nat} {β : BoundCtx τ n} {L R : LCtx τ}

/-- The remaining exits, with their positions in the original ordered list. -/
inductive ExitSuffix : LCtx τ → LCtx τ → Type u where
  | here {L : LCtx τ} : ExitSuffix L L
  | skip {L R : LCtx τ} (A : τ) : ExitSuffix L R → ExitSuffix (A :: L) R

def ExitSuffix.offset : {L R : LCtx τ} → ExitSuffix L R → Nat
  | _, _, .here => 0
  | _, _, .skip _ q => q.offset.succ

omit [TypeFormers τ] in
theorem ExitSuffix.at (q : ExitSuffix L R) {i : Nat} {A : τ} (h : At R i A) :
    At L (q.offset + i) A := by
  induction q with
  | here => simpa only [ExitSuffix.offset, Nat.zero_add] using h
  | skip B q ih =>
    change At (B :: _) (q.offset.succ + i) A
    rw [Nat.succ_add]
    exact ih h

/-- Dropping the current exit advances the original position by one. -/
def ExitSuffix.tail {A : τ} : {L : LCtx τ} → ExitSuffix L (A :: R) → ExitSuffix L R
  | _, .here => .skip A .here
  | _, .skip B q => .skip B q.tail

/-- Inject a suffix result back into the type of the full ordered list. -/
def ExitSuffix.inject : {L R : LCtx τ} → ExitSuffix L R → Operand Φ β (packedExitType R) →
    Operand Φ β (packedExitType L)
  | _, _, .here, a => a
  | _, _, .skip _ p, a =>
    let r := p.inject a
    ⟨.inr r.1, .inr r.2⟩

/-- Decode the packet by its tag. The empty tail uses native abort at the
fixed fallback position. Every case row reads only its incoming packet. -/
def decoder {i : Nat} {D : τ} (fallback : At L i D) :
    (R : LCtx τ) → ExitSuffix L R → Tree Φ β L (packedExitType R)
  | [], _ => .jump ⟨.abort (.bv 0), .abort .bv⟩ (.exit fallback)
  | _ :: R, q =>
    .case ⟨.bv 0, .bv⟩ (.exit (i := q.offset) (Nat.add_zero q.offset ▸ q.at (i := 0) rfl))
      (.local (decoder fallback R q.tail))

/-- Materialize an outer unary continuation as a block reading the original
captures and the incoming reply. Remaining computation runs inside typed
operands, followed by dispatch to the original ordered exits. -/
def Program.ofCode : {L : LCtx τ} → L ≠ [] → Code Φ β (packedExitType L) → Program Φ β L
  | [], h, _ => (h rfl).elim
  | A :: R, _, c =>
    let finish := decoder (rfl : At (A :: R) 0 A) (A :: R) .here
    match c with
    | .join entry body => ⟨_, entry.toLetCase, .jump body.toLetCase (.local finish)⟩
    | .let₁ entry body => ⟨_, entry, .jump body.toLetCase (.local finish)⟩
    | .br a => ⟨_, a, finish⟩
    | .let₂ a body => ⟨_, (Code.let₂ a body).toLetCase, finish⟩
    | .case e l r => ⟨_, (Code.case e l r).toLetCase, finish⟩

/-- Actual checked rows and entry for an arbitrary exact term with packed
result and a nonempty ordered interface. -/
def CheckedTable.ofLetCase {t : LetCase.LocallyNameless.Tm Empty Φ n} (h : L ≠ [])
    (d : LetCase.LocallyNameless.Derivation Φ (.nil : Ctx Empty τ) β t (packedExitType L)) :
    CheckedTable Φ β L :=
  let p := Program.ofCode h (Code.ofLetCase d)
  (show ResultGrammar p.toLetCase from ⟨p, rfl⟩).toTable

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
