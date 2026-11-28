module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithLetCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Defs

/-! # An effectful test, two effectful terms, and a shared region -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase.Example

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery
  (signature request Trace Exits)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit)

/-- The first request asks on the caller's Bit. -/
def test : Tm signature.Instr := .op (.ask false) (.var 0)

/-- The left arm asks again on the original capture. -/
def left : Tm signature.Instr := .op (.ask false) (.var 1)

/-- The right arm asks on the first reply's payload. -/
def right : Tm signature.Instr := .op (.ask true) (.var 0)

/-- Use the selected arm's reply tag to choose a typed exit.
Exit zero returns the original capture, and exit one forwards the reply payload. -/
def next : Region signature.Instr :=
  .case (.var 0) (.br 0 (.var 2)) (.br 1 (.var 0))

def source : Region signature.Instr := .let₁ (.case test left right) next

def target : Region signature.Instr := distributed test left right next

theorem test_typed : Tm.HasType [Bit] test Answer :=
  .op (f := (show signature.Instr from .ask false)) (.var (i := 0) rfl)

theorem left_typed : Tm.HasType [Bit, Bit] left Answer :=
  .op (f := (show signature.Instr from .ask false)) (.var (i := 1) rfl)

theorem right_typed : Tm.HasType [Bit, Bit] right Answer :=
  .op (f := (show signature.Instr from .ask true)) (.var (i := 0) rfl)

theorem next_typed : ValueBranches [Answer, Bit] next Exits :=
  .case (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.var (i := 2) rfl))
    (.br (ℓ := 1) rfl (.var (i := 0) rfl))

theorem source_typed : ValueBranches [Bit] source Exits :=
  .let₁ (.case test_typed left_typed right_typed) next_typed

theorem target_typed : ValueBranches [Bit] target Exits :=
  distributed_valueBranches test_typed left_typed right_typed next_typed

/-- Interpret the shared continuation at the original ordered exits. -/
def finish (g : Bool) : value Answer → Trace (value (packedExitType Exits))
  | .inl _ => pure (Sum.inl (bit g))
  | .inr a => pure (Sum.inr (Sum.inl a))

/-- The test runs once. Each reply tag selects one request and the same finish. -/
def expected (g : Bool) : Trace (value (packedExitType Exits)) :=
  request false (bit g) >>= fun
    | .inl _ => request false (bit g) >>= finish g
    | .inr a => request true a >>= finish g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase.Example
