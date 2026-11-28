module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Defs
import all Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Trace

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Open

open LetCase.Structural.Reply (run)
open Isotope.Semantics (BoundEnv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

local notation "Val" => LetCase.Structural.Finite.Value

variable {Φ : Type} [HasTy Φ (Ty Empty)] {d e m : Nat}
  {β : BoundCtx (Ty Empty) d} {δ : BoundCtx (Ty Empty) e} {K : LCtx (Ty Empty)}

set_option backward.isDefEq.respectTransparency false

private theorem rename_atRun (r : BoundCtx.Renaming β δ) (q : Table Φ β K m)
    (hq : q.check = true) (ok : (renameTable r q).check = true)
    (env : BoundEnv Val δ) (i : Fin (m + 1)) (x : Val (q.types i)) :
    atRun (renameTable r q) ok env i x = atRun q hq (pull r env) i x := by
  rw [atRun_row (renameTable r q), atRun_row q]
  change rowRun (renameBlock r (q.block i)) env (targetRun (atRun (renameTable r q) ok env)) x =
    rowRun (q.block i) (pull r env) (targetRun (atRun q hq (pull r env))) x
  generalize hb : q.block i = b
  have visit {X : Ty Empty} (t : Target q.types K X) (h : ∀ j ∈ t.locals, j ∈ b.locals) :
      targetRun (atRun (renameTable r q) ok env) t =
        targetRun (atRun q hq (pull r env)) t := by
    funext y
    cases t with
    | «local» k =>
      have edge : k ∈ q.localTargets i := by
        rw [Table.localTargets, hb]
        exact h k (by simp [Target.locals])
      exact rename_atRun r q hq ok env k y
    | exit _ => rfl
  cases b with
  | jump a t =>
    simp only [renameBlock, rowRun, run_rename, pull_up]
    rw [visit t (fun _ h => h)]
  | case a l h =>
    simp only [renameBlock, rowRun, run_rename, pull_up]
    rw [visit l (fun _ edge => List.mem_append_left _ edge),
      visit h (fun _ edge => List.mem_append_right _ edge)]
termination_by q.rank i
decreasing_by exact q.decreases hq edge

private theorem pull_underBinder {X Y : Ty Empty} (env : BoundEnv Val β) (x : Val X) (y : Val Y) :
    pull (BoundCtx.Renaming.underBinder β X Y) ((env.snoc x).snoc y) = env.snoc y := by
  rw [BoundCtx.Renaming.underBinder, pull_up]
  rfl

theorem underBinder_run_proof {X Y A : Ty Empty} (b : Operand Φ (β.snoc Y) A)
    (env : BoundEnv Val β) (x : Val X) (y : Val Y) :
    run (b.2.underBinder (X := X)) ((env.snoc x).snoc y) = run b.2 (env.snoc y) := by
  unfold LetCase.LocallyNameless.Derivation.underBinder
  rw [run_rename, pull_underBinder]

/-- Insert an unused older slot while keeping the newest input in place. -/
theorem weaken_receiver_run_proof {X Y : Ty Empty} (q : Table Φ (β.snoc Y) K m)
    (hq : q.check = true)
    (ok : (renameTable ((BoundCtx.Renaming.succ β X).up Y) q).check = true)
    (j : Fin (m + 1)) (a : Operand Φ (β.snoc Y) (q.types j))
    (env : BoundEnv Val β) (source : Val X) (input : Val Y) :
    run ((renameTable ((BoundCtx.Renaming.succ β X).up Y) q).toLetCase ok j
      ⟨_, a.2.rename ((BoundCtx.Renaming.succ β X).up Y)⟩).2 ((env.snoc source).snoc input) =
      run (q.toLetCase hq j a).2 (env.snoc input) := by
  rw [emit_run, emit_run]
  change (run (a.2.rename ((BoundCtx.Renaming.succ β X).up Y)) ((env.snoc source).snoc input) >>= _) = _
  rw [run_rename]
  have ambient : pull ((BoundCtx.Renaming.succ β X).up Y) ((env.snoc source).snoc input) = env.snoc input :=
    pull_underBinder env source input
  rw [ambient]
  congr 1
  funext x
  exact (rename_atRun _ q hq ok _ j x).trans (by rw [ambient])

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Open
