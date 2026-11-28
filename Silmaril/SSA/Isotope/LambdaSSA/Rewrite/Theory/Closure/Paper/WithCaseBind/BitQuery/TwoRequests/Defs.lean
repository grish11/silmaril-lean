module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs

/-! # Selected Bit queries under an earlier guard and a first reply -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit answer)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Table Assignment)

local notation "U" => (Ty.unit : Ty Empty)

/-- Slot zero is the first reply payload. Slot one is the earlier guarded Bit.
The first reply tag is recorded by the model and both tags use the same query table. -/
structure Program where
  firstLabel : Bool
  secondLabel : Bool
  secondQuery : Expr 2

/-- The first query is the guard bit. The second query table retains both
its guard coordinate and its first reply coordinate. -/
structure Key where
  firstLabel : Bool
  secondLabel : Bool
  secondQuery : Table 2

def Program.key (p : Program) : Key :=
  ⟨p.firstLabel, p.secondLabel, p.secondQuery.eval⟩

def assignment (guard reply : Bool) : Assignment 2 :=
  (Assignment.push Fin.elim0 guard).push reply

def literal (b : Bool) : Tm signature.Instr := constructorBit b .unit

/-- Select one literal query before invoking the second request. An expression
test is pure, and its two arms contain the only possible next invocation. -/
def compile (label : Bool) : {n : Nat} → Expr n → (Fin n → Tm signature.Instr) →
    Region signature.Instr
  | _, .literal b, _ => call label (literal b)
  | _, .read i, slots => .case (slots i) (call label (literal false)) (call label (literal true))
  | _, .split l r, slots =>
    let older := fun i => (slots i.succ).rename Nat.succ
    .case (slots 0) (compile label l older) (compile label r older)

theorem compile_typed (label : Bool) :
    {n : Nat} → (e : Expr n) → {Γ : VCtx (Ty Empty)} → {slots : Fin n → Tm signature.Instr} →
      (∀ i, Tm.HasType Γ (slots i) Bit) → ValueBranches Γ (compile label e slots) Exits
  | _, .literal b, _, _, _ => call_typed label (constructorBit_value b .unit).hasType
  | _, .read i, _, _, typed => .case (typed i) (call_typed label (.inl .unit)) (call_typed label (.inr .unit))
  | _, .split l r, Γ, _, typed =>
    let older := fun i => (typed (Fin.succ i)).rename (Ren.wk Γ U)
    .case (typed 0) (compile_typed label l older) (compile_typed label r older)

/-- The first request consumes the constructor selected by the prior case.
The same continuation is available at both reply tags. -/
def first (label guard : Bool) (next : Region signature.Instr) : Region signature.Instr :=
  .case (.op (.ask label) (literal guard)) next next

theorem first_typed (label guard : Bool) {Γ : VCtx (Ty Empty)} {next : Region signature.Instr}
    (h : ValueBranches (Bit :: Γ) next Exits) : ValueBranches Γ (first label guard next) Exits :=
  .case (.op (constructorBit_value guard .unit).hasType) h h

/-- In each guard branch, the exact constructor carries the native unit
payload at slot one. Slot zero is the later payload, read only after binding. -/
def guardedSlots (guard : Bool) : Fin 2 → Tm signature.Instr :=
  Fin.cases (.var 0) (fun _ => constructorBit guard (.var 1))

theorem guardedSlots_typed (guard : Bool) (i : Fin 2) :
    Tm.BranchValue [Bit, U, Bit] (guardedSlots guard i) Bit :=
  Fin.cases (.var (i := 0) rfl) (fun _ => constructorBit_value guard (.var (i := 1) rfl)) i

def Program.region (p : Program) : Region signature.Instr :=
  .case (.var 0)
    (first p.firstLabel false (compile p.secondLabel p.secondQuery (guardedSlots false)))
    (first p.firstLabel true (compile p.secondLabel p.secondQuery (guardedSlots true)))

theorem Program.typed (p : Program) : ValueBranches [Bit] p.region Exits :=
  .case (.var (i := 0) rfl)
    (first_typed p.firstLabel false (compile_typed _ _ (fun i => (guardedSlots_typed false i).hasType)))
    (first_typed p.firstLabel true (compile_typed _ _ (fun i => (guardedSlots_typed true i).hasType)))

/-- Quote in the fixed newest-first order after fixing the earlier guard
coordinate. The single remaining test inspects the runtime first reply. -/
def Key.row (k : Key) (guard : Bool) : Expr 1 :=
  Expr.quote 1 (fun env => k.secondQuery (assignment guard (env 0)))

def replySlot : Fin 1 → Tm signature.Instr := fun _ => .var 0

def Key.region (k : Key) : Region signature.Instr :=
  .case (.var 0)
    (first k.firstLabel false (compile k.secondLabel (k.row false) replySlot))
    (first k.firstLabel true (compile k.secondLabel (k.row true) replySlot))

theorem Key.typed (k : Key) : ValueBranches [Bit] k.region Exits :=
  .case (.var (i := 0) rfl)
    (first_typed k.firstLabel false (compile_typed _ _ (fun _ => .var (i := 0) rfl)))
    (first_typed k.firstLabel true (compile_typed _ _ (fun _ => .var (i := 0) rfl)))

def Program.packed (p : Program) :=
  Extension.Singleton.ofRegion Seed p.typed.packExits

def Key.packed (k : Key) :=
  Extension.Singleton.ofRegion Seed k.typed.packExits

abbrev Reply := Bool × Bool

/-- The event pair keeps the reply history and both actual query values. -/
def Key.word (k : Key) (guard : Bool) (firstReply secondReply : Reply) : FreeMonoid Event :=
  FreeMonoid.of ⟨k.firstLabel, guard, firstReply.1, firstReply.2⟩ *
  FreeMonoid.of ⟨k.secondLabel, k.secondQuery (assignment guard firstReply.2), secondReply.1, secondReply.2⟩

def Key.outcomes (k : Key) (guard : Bool) : Set (Except Bool (value (packedExitType Exits)) × FreeMonoid Event) :=
  Set.range fun replies : Reply × Reply =>
    (.ok (atExit (answer replies.2.1 replies.2.2)), k.word guard replies.1 replies.2)

noncomputable def Program.observations (p : Program) (guard : Bool) :=
  ((denote.map p.packed).of (bit guard)).outcomes

noncomputable def Key.observations (k : Key) (guard : Bool) :=
  ((denote.map k.packed).of (bit guard)).outcomes

namespace Example

/-- A compact XOR with a direct read of the earlier guard in the false-reply arm. -/
def xor : Program :=
  ⟨true, false, .split (.read 0) (.split (.literal true) (.literal false))⟩

def xorQuote : Program :=
  ⟨true, false, Expr.quote 2 xor.key.secondQuery⟩

def replyOnly : Program :=
  ⟨true, false, .read 0⟩

/-- Fix the first reply to right/false and the final reply to right/false.
Only the second query varies. -/
def observation (secondQuery : Bool) :
    Except Bool (value (packedExitType Exits)) × FreeMonoid Event :=
  (.ok (atExit (answer true false)),
    FreeMonoid.of ⟨true, true, true, false⟩ *
    FreeMonoid.of ⟨false, secondQuery, true, false⟩)

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests
