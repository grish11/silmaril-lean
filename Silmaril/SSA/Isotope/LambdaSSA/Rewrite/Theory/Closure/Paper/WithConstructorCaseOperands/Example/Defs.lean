module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Defs

/-! # Effectful constructor beta with a captured Bit and two ordered exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands.Example

open Paper.WithCaseBind.BitQuery
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

abbrev U := (Ty.unit : Ty Empty)

/-- Ask on the actual payload, then forward the reply payload from either tag. -/
def selected (i : Nat) : Tm signature.Instr :=
  .case (.op (.ask false) (.var i)) (.var 0) (.var 0)

/-- The dead arm has a visible request with the opposite label. -/
def dead : Tm signature.Instr :=
  .case (.op (.ask true) (.var 2)) (.var 0) (.var 0)

def source : Region signature.Instr :=
  .let₁ .unit (.case (.op (.ask true) (.case (.inl (.var 1)) (selected 0) dead))
    (.br 0 (.var 0)) (.br 1 (.var 0)))

def target : Region signature.Instr :=
  .let₁ .unit (.case (.op (.ask true) (selected 1)) (.br 0 (.var 0)) (.br 1 (.var 0)))

theorem selected_typed {Γ : VCtx (Ty Empty)} {i : Nat} (hi : At Γ i Bit) :
    Tm.HasType Γ (selected i) Bit :=
  .case (.op (f := (show signature.Instr from .ask false)) (.var hi))
    (.var (i := 0) rfl) (.var (i := 0) rfl)

theorem dead_typed : Tm.HasType [U, U, Bit] dead Bit :=
  .case (.op (f := (show signature.Instr from .ask true)) (.var (i := 2) rfl))
    (.var (i := 0) rfl) (.var (i := 0) rfl)

theorem exitLeft : ValueBranches [Bit, U, Bit] (.br 0 (.var 0) : Region signature.Instr) Exits :=
  .br (ℓ := 0) rfl (.var (i := 0) rfl)

theorem exitRight : ValueBranches [Bit, U, Bit] (.br 1 (.var 0) : Region signature.Instr) Exits :=
  .br (ℓ := 1) rfl (.var (i := 0) rfl)

theorem source_typed : ValueBranches [Bit] source Exits :=
  .let₁ .unit (.case (.op (f := (show signature.Instr from .ask true))
    (.case (.inl (.var (i := 1) rfl)) (selected_typed (i := 0) rfl) dead_typed)) exitLeft exitRight)

theorem target_typed : ValueBranches [Bit] target Exits :=
  .let₁ .unit (.case (.op (f := (show signature.Instr from .ask true))
    (selected_typed (i := 1) rfl)) exitLeft exitRight)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands.Example
