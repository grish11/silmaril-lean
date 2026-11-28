module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Boundary.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region.Paper
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.UnaryReturn.Beta.Constructors (pairSequence)
open LetCase.Structural.Finite (Shape)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private abbrev bit : Shape := .sum .unit .unit
private abbrev X := bit.ty
private abbrev U := (Ty.unit : Ty Empty)
private abbrev P := Ty.product X X
private abbrev β : BoundCtx (Ty Empty) 1 := .snoc .nil X

private instance : LetCase.Structural.Finite.Signature Unit where
  source _ := bit
  target _ := bit

private abbrev left : Tm Unit := .let₁ (.var 1) (.var 0)
private abbrev right : Tm Unit := .var 1
private abbrev other : Region Unit := .br 0 (.pair (.var 1) (.var 1))
private abbrev block : Region Unit := .br 1 (.var 0)
private abbrev test : Tm Unit := .op () (.var 0)

private theorem pair_at_local_label :
    WithConstructorSequencing.Joined.Eqv false [U, X]
      (returnOnce (.pair left right)) (pairSequence left right) [P, P] := by
  have older : Tm.BranchValue [U, X] right X := .var rfl
  have newer : Tm.BranchValue [X, U, X] (Tm.var 0 : Tm Unit) X := .var rfl
  have step : WithConstructorSequencing.Step [U, X]
      (returnOnce (.pair left right)) (pairSequence left right) [P] :=
    .pair (.let₁ (.value older) (.value newer)) (.value older)
  have h : WithConstructorSequencing.Joined.Eqv false [U, X]
      (returnOnce (.pair left right)) (pairSequence left right) [P] :=
    .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inr step)
  have labels : Ren [P] [P, P] id := by
    intro i A hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  simpa only [Region.renameLabels_id] using h.renameLabels labels

private def before : Region Unit :=
  .cfg (.case test (returnOnce (.pair left right)) other) 1 (fun _ => block)

private def after : Region Unit :=
  .cfg (.case test (pairSequence left right) other) 1 (fun _ => block)

private theorem rewritten : WithConstructorSequencing.Joined.Eqv false [X] before after [P] := by
  have sameArm : Region.HasType [U, X] other [P, P] :=
    .br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 1) rfl))
  have sameBlock : Region.HasType [P, X] block [P, P] := .br (ℓ := 1) rfl (.var (i := 0) rfl)
  exact .cfg (fun _ : Fin 1 => P)
    (.case (.op (.var (i := 0) rfl)) pair_at_local_label (.refl sameArm))
    (fun _ => .refl sameBlock)

private def source : Endpoint Unit β P :=
  ⟨before, rewritten.typed.1, .join (.case _ (.let₁ _ (.br _)) (.br _)) (.br _)⟩

private def target : Endpoint Unit β P :=
  ⟨after, rewritten.typed.2, .join (.case _ (.let₁ _ (.let₁ _ (.br _))) (.br _)) (.br _)⟩

-- The source is open at a genuine binary sum. The primitive is the shared
-- discriminator, and the sequenced pair still reads the captured older bit.
example : source.ConstructorEqv target := rewritten

example : LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ β
    source.compile.1 target.compile.1 P :=
  (source.valid_iff_compiled (.snoc .nil bit) target).mp (Endpoint.constructor_sound (p := source) (q := target) rewritten)

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
