module

import Silmaril.Languages.Starlark.Lists.Thms

namespace Silmaril.Languages.Starlark.Lists

deriving instance DecidableEq for Except

private def int (n : Int) : Expr := .scalar (.int n)

private def global (name : String) : Binding := ⟨.global, name⟩

private def read (name : String) : Expr := .read (.bound (global name))

private def assign (name : String) (rhs : Expr) : Stmt := .assign (global name) rhs

private def listOf (items : List Expr) : Expr := .list (items.foldr Code.cons .empty)

private def suite (stmts : List Stmt) : Stmt := stmts.foldr Code.seq .pass

private def result {α : Type} : Outcome α → Except Error α
  | .ok value _ => .ok value
  | .error error _ => .error error

private def finalState {α : Type} : Outcome α → State
  | .ok _ state | .error _ state => state

private def inState {α : Type} (setup : Stmt) (test : Meaning α) : Outcome α :=
  Outcome.resume (denote setup {}) fun () => test

private def aliasProgram : Stmt := suite
  [assign "x" (listOf [int 10]), assign "y" (read "x"), assign "other" (listOf [int 10]),
   assign "appended" (.append (read "x") (int 11)), .setIndex (read "y") (int (-1)) (int 12),
   assign "observed" (.index (read "x") (int (-1))),
   assign "independent" (.index (read "other") (int 0))]

-- Copying a reference preserves identity. Equal contents in two literals still allocate twice.
example :
    let out := denote aliasProgram {}
    let state := finalState out
    result out = .ok () ∧
    state.bindings (global "x") = some (.list 0) ∧
    state.bindings (global "y") = some (.list 0) ∧
    state.bindings (global "other") = some (.list 1) ∧
    state.bindings (global "appended") = some (.scalar .none) ∧
    state.bindings (global "observed") = some (.scalar (.int 12)) ∧
    state.bindings (global "independent") = some (.scalar (.int 10)) :=
  by decide +kernel

private def cyclicProgram : Stmt := suite
  [assign "leaf" (listOf [int 42]), assign "inner" (listOf [read "leaf"]),
   assign "outer" (listOf [read "inner"]), assign "alias" (read "inner"),
   assign "spare" (listOf []), .eval (.append (read "inner") (read "outer")),
   .eval (.append (read "inner") (read "inner"))]

private def frozenCycle : Outcome Unit :=
  inState cyclicProgram fun state =>
    Outcome.resume (state.read (.bound (global "outer"))) fun root state =>
      .ok () (state.freeze [root])

-- outer -> inner -> leaf, inner -> outer, and inner -> inner.
-- The unrelated spare remains mutable and a later empty freeze preserves existing flags.
example :
    let state := finalState frozenCycle
    result frozenCycle = .ok () ∧
    state.heap.toList.map Cell.frozen = [true, true, true, false] ∧
    (state.freeze []).heap = state.heap ∧
    state.bindings (global "alias") = some (.list 1) ∧
    result (denote (.index (.index (read "alias") (int 0)) (int 0)) state) =
      .ok (.scalar (.int 42)) ∧
    result (denote (.append (read "spare") (int 5)) state) = .ok (.scalar .none) :=
  by decide +kernel

example :
    let state := finalState frozenCycle
    let append := denote (.append (read "alias") (int 0)) state
    let replace := denote (.setIndex (read "inner") (int (-1)) (int 0)) state
    result append = .error (.frozen 1) ∧
    result replace = .error (.frozen 1) ∧
    (finalState append).heap = state.heap ∧ (finalState replace).heap = state.heap :=
  by decide +kernel

-- A very large index is still an exact integer and fails the bounds check.
example :
    result (denote (.index (listOf [int 10]) (int (-2))) {}) =
      .error (.indexRange (-2) 1) ∧
    result (denote (.index (listOf [int 10]) (.scalar (.bool true))) {}) =
      .error .indexType ∧
    result (denote (.index (listOf [int 10]) (int 18446744073709551616)) {}) =
      .error (.indexRange 18446744073709551616 1) ∧
    result (denote (.index (int 1) (int 0)) {}) = .error .indexTarget :=
  by decide +kernel

-- Assignment evaluates its RHS first. The receiver reads the just-appended 9,
-- then fails because an integer cannot be the assignment target.
example :
    let out := inState (assign "a" (listOf [])) <|
      denote (.setIndex (.index (read "a") (int 0)) (int 0) (.append (read "a") (int 9)))
    result out = .error .assignmentTarget ∧
    (finalState out).heap = #[⟨.list [.scalar (.int 9)], false⟩] :=
  by decide +kernel

-- Literal operands run left to right. Index failure retains the preceding
-- append and skips the later operand and the outer allocation.
example :
    let out := inState (assign "a" (listOf [])) <|
      denote (listOf [.append (read "a") (int 4), .index (read "a") (int 4),
        .append (read "a") (int 5)])
    result out = .error (.indexRange 4 1) ∧
    (finalState out).heap = #[⟨.list [.scalar (.int 4)], false⟩] :=
  by decide +kernel

-- Method lookup on a scalar fails before the argument can have an effect.
example :
    let out := inState (assign "a" (listOf [])) <|
      denote (.append (int 1) (.append (read "a") (int 9)))
    result out = .error .appendTarget ∧ (finalState out).heap = #[⟨.list [], false⟩] :=
  by decide +kernel

end Silmaril.Languages.Starlark.Lists
