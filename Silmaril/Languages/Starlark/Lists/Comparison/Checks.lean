module

import Silmaril.Languages.Starlark.Functions.Lowering.Thms
import Silmaril.Languages.Starlark.Lists.Thms
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Denotation.Defs

namespace Silmaril.Languages.Starlark.Lists.Comparison

open Functions.Lowering (AtomSafe Evaluates lower lower_preserves StateMatch)

deriving instance DecidableEq for Except

private def int (n : Int) : Value := .scalar (.int n)

private def result {α : Type} : Outcome α → Except Error α
  | .ok value _ => .ok value
  | .error error _ => .error error

-- Numeric normalization is lifted through separately allocated nested tuples.
-- The equal pair also has the same canonical code and reaches the same dictionary entry.
#guard
  let edge := Int.shiftLeft 1 53
  let action : Meaning (Bool × Bool × Bool × Bool × Bool × Value) := do
    let ints ← allocateTuple [int edge, int 0, .scalar (.float 0x7ff8000000000021)]
    let floats ← allocateTuple [.scalar (.float 0x4340000000000000), .scalar (.float 0x8000000000000000),
      .scalar (.float 0xfff0000000000001)]
    let large ← allocateTuple [int (edge + 1), int 0, .scalar (.float 0x7ff8000000000021)]
    let left ← allocateTuple [.string "tag", ints]
    let right ← allocateTuple [.string "tag", floats]
    let different ← allocateTuple [.string "tag", large]
    let candidates ← allocateTuple [different, right]
    let bools ← allocateTuple [.scalar (.bool false)]
    let zeros ← allocateTuple [int 0]
    let dict ← allocateDict []
    writeIndex dict left (.string "found")
    let found ← readIndex dict right
    fun state => fromExcept (do
      let same ← evaluate state.heap .eq left right
      let unequal ← evaluate state.heap .ne left different
      let member ← evaluate state.heap .mem left candidates
      let boolDistinct ← evaluate state.heap .ne bools zeros
      let a ← state.keyOf left
      let b ← state.keyOf right
      pure (same, unequal, member, boolDistinct, a == b, found)) state
  result (action {}) = .ok (true, true, true, true, true, .string "found")

-- Length and field order suppress unreached errors. A visited field gets the
-- left read first. A membership hit suppresses later entries, and errors are
-- preserved by both negated operators.
#guard
  let state : State := { heap := #[
    ⟨.tuple [int 1, .tuple 42] none, false⟩,
    ⟨.tuple [int 0, .tuple 43] none, false⟩,
    ⟨.tuple [int 1, .tuple 43] none, false⟩,
    ⟨.tuple [.tuple 42] none, false⟩,
    ⟨.tuple [.builtin .len, int 1] none, false⟩,
    ⟨.tuple [int 1, .builtin .len] none, false⟩,
    ⟨.tuple [.builtin .len] none, false⟩,
    ⟨.dict [], false⟩,
    ⟨.tuple [.tuple 7, .tuple 42] none, false⟩] }
  evaluate state.heap .eq (.tuple 0) (.tuple 1) = .ok false ∧
    evaluate state.heap .eq (.tuple 3) (.tuple 0) = .ok false ∧
    evaluate state.heap .eq (.tuple 0) (.tuple 2) = .error (.danglingAddress 42) ∧
    evaluate state.heap .ne (.tuple 0) (.tuple 8) = .ok true ∧
    evaluate state.heap .ne (.tuple 2) (.tuple 0) = .error (.danglingAddress 43) ∧
    evaluate state.heap .eq (.tuple 8) (.tuple 8) = .error (.wrongCellKind 7) ∧
    evaluate state.heap .mem (int 1) (.tuple 5) = .ok true ∧
    evaluate state.heap .notMem (int 1) (.tuple 5) = .ok false ∧
    evaluate state.heap .notMem (int 1) (.tuple 3) = .ok true ∧
    evaluate state.heap .mem (int 1) (.tuple 4) = .error (.comparisonType (.builtin .len) (int 1)) ∧
    evaluate state.heap .notMem (int 1) (.tuple 4) = .error (.comparisonType (.builtin .len) (int 1)) ∧
    evaluate state.heap .eq (.tuple 6) (.tuple 6) = .error (.comparisonType (.builtin .len) (.builtin .len)) ∧
    evaluate state.heap .mem (int 1) (.dict 7) = .ok false

-- Nine singleton tuple levels plus the scalar use all ten comparisons.
-- Membership grants the candidate the same ten levels as top-level equality.
#guard
  let wrap := fun count value =>
    (List.range count).foldlM (fun field _ => allocateTuple [field]) value
  let action : Meaning (Except Error Bool × Except Error Bool × Except Error Bool × Except Error Bool) := do
    let nine ← wrap 9 (int 0)
    let nineFloat ← wrap 9 (.scalar (.float 0x8000000000000000))
    let ten ← allocateTuple [nine]
    let tenFloat ← allocateTuple [nineFloat]
    let candidates ← allocateTuple [ten]
    fun state => .ok (evaluate state.heap .eq nine nineFloat, evaluate state.heap .eq ten tenFloat,
      evaluate state.heap .mem nineFloat ten, evaluate state.heap .mem tenFloat candidates) state
  result (action {}) = .ok (.ok true, .error .comparisonDepth, .ok true, .error .comparisonDepth)

-- List and tuple fields share the same recursive numeric comparison, and
-- different sequence kinds remain unequal even with the same fields.
#guard
  let action : Meaning (Bool × Bool × Bool × Bool × Bool) := do
    let leftLeaf ← allocate [int 9007199254740992, int 0, .scalar (.float 0x7ff8000000000021)]
    let rightLeaf ← allocate [.scalar (.float 0x4340000000000000), .scalar (.float 0x8000000000000000),
      .scalar (.float 0xfff0000000000001)]
    let leftTuple ← allocateTuple [leftLeaf]
    let rightTuple ← allocateTuple [rightLeaf]
    let left ← allocate [leftTuple]
    let right ← allocate [rightTuple]
    let differentKind ← allocateTuple [leftTuple]
    let bools ← allocate [.scalar (.bool false)]
    let zeros ← allocate [int 0]
    let candidates ← allocate [bools, right]
    fun state => fromExcept (do
      let same ← evaluate state.heap .eq left right
      let found ← evaluate state.heap .mem left candidates
      let kinds ← evaluate state.heap .ne left differentKind
      let boolDistinct ← evaluate state.heap .ne bools zeros
      let selfNaN ← evaluate state.heap .eq leftLeaf leftLeaf
      pure (same, found, kinds, boolDistinct, selfNaN)) state
  result (action {}) = .ok (true, true, true, true, true)

-- Identical addresses still traverse fields. Length, an early mismatch, or
-- a membership hit can skip the later read, but reached errors keep priority.
#guard
  let state : State := { heap := #[
    ⟨.list [int 0, .list 0], false⟩,
    ⟨.list [int 1, .list 1], false⟩,
    ⟨.list [.list 0], false⟩,
    ⟨.list [int 0, .list 3], false⟩,
    ⟨.list [.tuple 5], false⟩,
    ⟨.tuple [.list 4] none, false⟩,
    ⟨.list [.list 8, .list 42], false⟩,
    ⟨.list [.list 42, .list 8], false⟩,
    ⟨.list [int 1], true⟩,
    ⟨.dict [], false⟩, ⟨.list [.dict 9], false⟩] }
  evaluate state.heap .eq (.list 0) (.list 2) = .ok false ∧
    evaluate state.heap .eq (.list 0) (.list 1) = .ok false ∧
    evaluate state.heap .eq (.list 0) (.list 3) = .error .comparisonDepth ∧
    evaluate state.heap .eq (.list 0) (.list 0) = .error .comparisonDepth ∧
    evaluate state.heap .ne (.list 4) (.list 4) = .error .comparisonDepth ∧
    evaluate state.heap .mem (.list 0) (.list 2) = .error .comparisonDepth ∧
    evaluate state.heap .mem (.list 8) (.list 6) = .ok true ∧
    evaluate state.heap .notMem (.list 8) (.list 7) = .error (.danglingAddress 42) ∧
    evaluate state.heap .eq (.list 42) (.list 5) = .error (.danglingAddress 42) ∧
    evaluate state.heap .eq (.list 8) (.list 5) = .error (.wrongCellKind 5) ∧
    evaluate state.heap .mem (int 1) (.list 8) = .ok true ∧
    evaluate state.heap .mem (int 1) (.list 5) = .error (.wrongCellKind 5) ∧
    evaluate state.heap .eq (.list 10) (.list 10) = .ok true

-- An alternating chain consumes one budget unit per reached pair, regardless
-- of the container kind. The list membership receiver does not consume it.
#guard
  let wrap := fun (count : Nat) (leaf : Value) =>
    (List.range count).foldlM (fun field level =>
      if level % 2 = 0 then allocate [field] else allocateTuple [field]) leaf
  let action : Meaning (List (Except Error Bool)) := do
    let nine ← wrap 9 (int 0)
    let nineFloat ← wrap 9 (.scalar (.float 0x8000000000000000))
    let ten ← allocateTuple [nine]
    let tenFloat ← allocateTuple [nineFloat]
    let shallowCandidate ← allocate [nine]
    let deepCandidate ← allocate [ten]
    let earlyLeft ← allocate [int 0, ten]
    let earlyRight ← allocate [int 1, tenFloat]
    fun state => .ok [evaluate state.heap .eq nine nineFloat, evaluate state.heap .eq ten tenFloat,
      evaluate state.heap .mem nineFloat shallowCandidate, evaluate state.heap .mem tenFloat deepCandidate,
      evaluate state.heap .eq earlyLeft earlyRight] state
  result (action {}) = .ok [.ok true, .error .comparisonDepth, .ok true, .error .comparisonDepth, .ok false]

private def events : Binding := ⟨.global, "events"⟩
private def output : Binding := ⟨.global, "output"⟩

private def initial : State :=
  { heap := #[⟨.list [], false⟩]
    bindings := fun name => if name = events then some (.list 0) else none }

private def mark (n : Int) : Expr := .append (.read (.bound events)) (.scalar (.int n))

private def left : Expr := .tuple (.cons (mark 1) .empty)
private def right : Expr := .tuple (.cons (mark 2) (.cons (.builtin .len) .empty))

private def reached : State :=
  { initial with heap := #[⟨.list [int 1, int 2], false⟩, ⟨.tuple [.scalar .none] (some
      [.openTuple, .scalar .none, .closeTuple]), false⟩,
    ⟨.tuple [.scalar .none, .builtin .len] (some
      [.openTuple, .scalar .none, .builtin .len, .closeTuple]), false⟩] }

-- A type error after comparing the left tuple against the right tuple's first
-- scalar must leave both operands evaluated before it is reported.
private def failure : Expr := .compare .mem left right

example : denote failure initial = .error (.comparisonType (.builtin .len) (.tuple 1)) reached := rfl

-- A failed operand stops the other operand or the comparison, respectively.
example : denote (.compare .eq (.read (.bound output)) (mark 2)) initial =
    .error (.uninitialized output) initial := rfl

example : denote (.compare .eq left (.read (.bound output))) initial =
    .error (.uninitialized output) { reached with heap := #[
      ⟨.list [int 1], false⟩, ⟨.tuple [.scalar .none] (some [.openTuple, .scalar .none, .closeTuple]), false⟩] } :=
  rfl

private theorem visible (name : String) : ¬ Functions.Lowering.Scratch 0 ⟨.global, name⟩ := by
  rintro ⟨index, _, equal⟩
  simp [Functions.Lowering.temporary] at equal

private theorem mark_safe (n : Int) : AtomSafe (mark n) :=
  .append (.bound (visible "events")) (.scalar _)

example :
    ∃ final, Functions.denoteBody #[] [] (lower (.atom failure) output).code initial =
        .error (.comparisonType (.builtin .len) (.tuple 1)) final ∧
      StateMatch 0 reached final := by
  have safe : AtomSafe failure :=
    .compare (.tuple (.cons (mark_safe 1) .empty))
      (.tuple (.cons (mark_safe 2) (.cons (.builtin .len) .empty)))
  have ran : Evaluates #[] [] initial (.atom failure) (.error (.comparisonType (.builtin .len) (.tuple 1)) reached) :=
    .atom safe ((eval_iff_denote ..).mpr rfl)
  exact lower_preserves ran (by intro _; rfl) output (visible "output")

private def beforeMutation : State :=
  { heap := #[⟨.list [int 1], false⟩, ⟨.list [int 1, int 2], false⟩]
    bindings := fun name => if name = events then some (.list 0)
      else if name = output then some (.list 1) else none }

private def mutation : Expr :=
  .compare .eq (.read (.bound events))
    (.index (.tuple (.cons (mark 2) (.cons (.read (.bound output)) .empty))) (.scalar (.int 1)))

-- The left operand yields its address before the right operand appends. The
-- comparison reads the updated elements and leaves that mutation in the state.
example : denote mutation beforeMutation = .ok (.scalar (.bool true))
    { beforeMutation with heap := #[⟨.list [int 1, int 2], false⟩, ⟨.list [int 1, int 2], false⟩,
        ⟨.tuple [.scalar .none, .list 1] none, false⟩] } := rfl

-- A cycle created during operand evaluation stays in the reached heap when
-- comparing the two aliases exhausts the budget.
example :
    let receiver : Expr := .read (.bound events)
    let right : Expr := .index (.tuple (.cons (.append receiver receiver) (.cons receiver .empty)))
      (.scalar (.int 1))
    denote (.compare .eq receiver right) initial = .error .comparisonDepth
      { initial with heap := #[⟨.list [.list 0], false⟩, ⟨.tuple [.scalar .none, .list 0] none, false⟩] } :=
  rfl

end Silmaril.Languages.Starlark.Lists.Comparison
