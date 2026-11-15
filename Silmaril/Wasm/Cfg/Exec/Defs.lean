module

public import Silmaril.Wasm.Cfg.BlockTree.Defs
public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.SingleThreaded.Determinism.Family

@[expose] public section

/-!
# Where a running body is: the position invariant (operational bridge, milestone 1)

Core 3.0 runs structured control by rewriting: entering `block`/`loop`/`try_table` wraps the
body in `LABEL_n{cont}` (and `HANDLER_n{catch*}`), `if` becomes a `block` of the chosen arm,
and `br`/`return`/traps/exceptions bubble outwards through these contexts. `Resid is l code`
says that `code` is a configuration's code *while running the sequence `is` at location `l`*:

* `.at j` — about to run instruction `j` of `is` (`j = is.length`: done), with values below;
* `.inArm k a l` — inside arm `a` of the structured instruction at index `k`, at `l` there,
  with the rest of `is` after `k` waiting outside the label;
* `.ifArm k a` — the `if` at `k` has chosen arm `a` and is about to enter it as a `block`;
* `.mid j` — instruction `j` has started and left simple code `B` (values and non-control
  instructions, as expanding rules such as `memory.fill` do) before the rest of `is`;
* `.exiting` — an exit kernel (`br`, `return`, `trap`, a thrown exception) is bubbling out,
  followed by code it discards.

The relation is stated against the Core 3.0 syntax (`Admin`, `vals`, `expression`); the step
preservation theorems and the projection to the block CFG (`Cfg.Edge`) are the next milestones
(`docs/projects/wasm-cfg.md`, "Plan: execution follows the CFG"). Label arities are left free
here; typing fixes them.
-/

namespace Silmaril.Wasm.Cfg

open Silmaril.Wasm.Execution.Core

/-- A location in a sequence of a running body. -/
inductive Loc where
  | at (j : Nat)
  | inArm (k a : Nat) (l : Loc)
  | ifArm (k a : Nat)
  | mid (j : Nat)
  | exiting
  deriving DecidableEq, Repr

/-- The exit kernels that bubble out of labels, handlers and frames (call-free fragment). -/
inductive ExitKernel : List Admin → Prop where
  | br (l : LabelIdx) : ExitKernel [.plain (.br l)]
  | ret : ExitKernel [.plain .return_]
  | trap : ExitKernel [.trap]
  | throw (a : Nat) : ExitKernel (throwing a)

/-! ## Non-control steps (milestone 2, first part) -/

/-- An administrative instruction that is a value, or a plain instruction of a non-control
reduction family (`Det.famOf`: parametric, numeric, vector, variable, table, memory, reference,
aggregate). -/
def SimpleAdmin (a : Admin) : Prop :=
  a.val? ≠ none ∨ ∃ i, a = .plain i ∧ SingleThreaded.Det.famOf (.plain i) ≠ .control

/-- **The position invariant**: `code` runs the sequence `is` at location `l`. -/
inductive Resid : List Instr → Loc → List Admin → Prop where
  | at {is : List Instr} {j : Nat} (vs : List Val) (hj : j ≤ is.length) :
      Resid is (.at j) (vals vs ++ expression (is.drop j))
  | inBlock {is b : List Instr} {k : Nat} {bt : BlockType} {l : Loc} {inner : List Admin}
      (vs : List Val) (n : Nat) (hk : is[k]? = some (.block bt b)) (h : Resid b l inner) :
      Resid is (.inArm k 0 l) (vals vs ++ [.label n [] inner] ++ expression (is.drop (k + 1)))
  | inLoop {is b : List Instr} {k : Nat} {bt : BlockType} {l : Loc} {inner : List Admin}
      (vs : List Val) (n : Nat) (hk : is[k]? = some (.loop bt b)) (h : Resid b l inner) :
      Resid is (.inArm k 0 l)
        (vals vs ++ [.label n [.loop bt b] inner] ++ expression (is.drop (k + 1)))
  | inIf {is c t e : List Instr} {k a : Nat} {bt : BlockType} {l : Loc} {inner : List Admin}
      (vs : List Val) (n : Nat) (hk : is[k]? = some (.if_ bt t e))
      (ha : armOf (.if_ bt t e) a = some c) (h : Resid c l inner) :
      Resid is (.inArm k a l) (vals vs ++ [.label n [] inner] ++ expression (is.drop (k + 1)))
  | inTry {is b : List Instr} {k : Nat} {bt : BlockType} {cs : List Catch} {l : Loc}
      {inner : List Admin} (vs : List Val) (n m : Nat) (hk : is[k]? = some (.tryTable bt cs b))
      (h : Resid b l inner) :
      Resid is (.inArm k 0 l)
        (vals vs ++ [.handler n cs [.label m [] inner]] ++ expression (is.drop (k + 1)))
  | ifArm {is c t e : List Instr} {k a : Nat} {bt : BlockType} (vs : List Val)
      (hk : is[k]? = some (.if_ bt t e)) (ha : armOf (.if_ bt t e) a = some c) :
      Resid is (.ifArm k a) (vals vs ++ [.plain (.block bt c)] ++ expression (is.drop (k + 1)))
  | exiting {is : List Instr} {x rest : List Admin} (vs : List Val) (hx : ExitKernel x) :
      Resid is .exiting (vals vs ++ x ++ rest)
  | mid {is : List Instr} {j : Nat} (B : List Admin) (hB : ∀ b ∈ B, SimpleAdmin b)
      (hj : j < is.length) :
      Resid is (.mid j) (B ++ expression (is.drop (j + 1)))

/-- A body's code inside its call frame: `FRAME_n{f} (LABEL_n{} …)` around a residual. -/
inductive InFrame (body : Expr) : Loc → List Admin → Prop where
  | frame {n m : Nat} {fr : Frame} {l : Loc} {inner : List Admin} (h : Resid body l inner) :
      InFrame body l [.frame n fr [.label m [] inner]]

/-- What a non-control reduction may leave: simple administrative instructions only, or a
trap. Some non-control rules expand into further instructions (`memory.fill`, `table.copy`,
…), hence the second disjunct of `SimpleAdmin`. -/
def SimpleRes (is' : List Admin) : Prop := (∀ a ∈ is', SimpleAdmin a) ∨ is' = [.trap]

/-- What a Core step from `val* a` (with `a` non-control) leaves: simple code, or values
followed by a trap. -/
def StepRes (x : List Admin) : Prop := (∀ a ∈ x, SimpleAdmin a) ∨ ∃ ws, x = vals ws ++ [.trap]

end Silmaril.Wasm.Cfg
