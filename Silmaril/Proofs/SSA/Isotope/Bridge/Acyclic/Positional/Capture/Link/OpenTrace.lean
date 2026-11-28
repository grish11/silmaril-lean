module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Defs
public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Thms
import all Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Trace

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Open

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Reply (run)
open Isotope.Semantics (BoundEnv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

local notation "Val" => LetCase.Structural.Finite.Value
local notation "Trace" => LetSeq.StraightLine.Structural.Trace Empty
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty Empty))

variable {Φ : Type} [HasTy Φ (Ty Empty)] {d e m N : Nat}
  {β : BoundCtx (Ty Empty) d} {δ : BoundCtx (Ty Empty) e}
  {P A B D : Ty Empty} {K : LCtx (Ty Empty)} {R : Fin N → Ty Empty}

set_option backward.isDefEq.respectTransparency false

private def payload {X : Ty Empty} (t : Target R K X) (saved : Val P) (x : Val X) :
    Val (packetType P t) :=
  match t with
  | .local _ => (saved, x)
  | .exit _ => x

private theorem run_packet (t : Target R K B) (capture : Operand Φ δ P) (value : Operand Φ δ B)
    (env : BoundEnv Val δ) (saved : Val P) (hc : run capture.2 env = pure saved) :
    run (packet t capture value).2 env =
      (run value.2 env >>= fun x => pure (payload t saved x)) := by
  cases t with
  | «local» i =>
    change (run capture.2 env >>= fun c => run value.2 env >>= fun x => pure (c, x)) = _
    rw [hc, pure_bind]
    rfl
  | exit h => exact (bind_pure _).symm

private def packetEnv (env : BoundEnv Val β) (saved : Val P) (x : Val A) :
    BoundEnv Val (splitContext β P A) :=
  ((env.snoc (A := Ty.product P A) (saved, x)).snoc saved).snoc x

private theorem run_unpack (body : Operand Φ (splitContext β P A) B)
    (env : BoundEnv Val β) (saved : Val P) (x : Val A) :
    run (unpack body).2 (env.snoc (A := Ty.product P A) (saved, x)) =
      run body.2 (packetEnv env saved x) := by
  simp only [unpack, run, Derivation.denote, pure_bind]
  rfl

private theorem run_read (a : Operand Φ ((β.snoc P).snoc A) B)
    (env : BoundEnv Val β) (saved : Val P) (x : Val A) :
    run (readOriginal a).2 (packetEnv env saved x) =
      run a.2 ((env.snoc saved).snoc x) := by
  simp only [readOriginal, run_rename, packetEnv, pull_up]
  rfl

private theorem run_arm (t : Target R K B)
    (env : BoundEnv Val (splitContext β P A)) (x : Val B) :
    run (packet (Φ := Φ) t (δ := (splitContext β P A).snoc B) ⟨.bv 2, .bv⟩ ⟨.bv 0, .bv⟩).2 (env.snoc x) =
      pure (payload t (env 1) x) := by
  rw [run_packet _ _ _ _ (env 1) rfl]
  exact pure_bind _ _

private theorem run_casePacket (a : Operand Φ ((β.snoc P).snoc A) (.coprod B D))
    (l : Target R K B) (r : Target R K D) (env : BoundEnv Val β) (saved : Val P) (x : Val A) :
    run (casePacket a l r).2 (packetEnv env saved x) =
      (run a.2 ((env.snoc saved).snoc x) >>= fun sum =>
        pure (Sum.elim (fun y => Sum.inl (payload l saved y)) (fun y => Sum.inr (payload r saved y)) sum)) := by
  simp only [casePacket, run_case, run_read]
  congr 1
  funext sum
  cases sum with
  | inl y =>
    simp only [Sum.elim_inl]
    change (run (packet l (δ := (splitContext β P A).snoc B) ⟨.bv 2, .bv⟩ ⟨.bv 0, .bv⟩).2
      ((packetEnv env saved x).snoc y) >>= fun z => pure (Sum.inl z)) = _
    rw [run_arm, pure_bind]
    rfl
  | inr y =>
    simp only [Sum.elim_inr]
    change (run (packet r (δ := (splitContext β P A).snoc D) ⟨.bv 2, .bv⟩ ⟨.bv 0, .bv⟩).2
      ((packetEnv env saved x).snoc y) >>= fun z => pure (Sum.inr z)) = _
    rw [run_arm, pure_bind]
    rfl

private theorem carry_at_run (q : Table Φ (β.snoc P) K m)
    (hq : q.check = true) (ok : (carry q).check = true)
    (env : BoundEnv Val β) (saved : Val P) (i : Fin (m + 1)) (x : Val (q.types i)) :
    atRun (carry q) ok env i (saved, x) = atRun q hq (env.snoc saved) i x := by
  rw [atRun_row (carry q), atRun_row q]
  change rowRun (block (q.block i)) env (targetRun (atRun (carry q) ok env)) (saved, x) =
    rowRun (q.block i) (env.snoc saved) (targetRun (atRun q hq (env.snoc saved))) x
  generalize hb : q.block i = b
  have visit {X : Ty Empty} (t : Target q.types K X) (h : ∀ j ∈ t.locals, j ∈ b.locals) (y : Val X) :
      targetRun (atRun (carry q) ok env) (target t) (payload t saved y) =
        targetRun (atRun q hq (env.snoc saved)) t y := by
    cases t with
    | «local» k =>
      have edge : k ∈ q.localTargets i := by
        rw [Table.localTargets, hb]
        exact h k (by simp [Target.locals])
      exact carry_at_run q hq ok env saved k y
    | exit h => rfl
  cases b with
  | jump a t =>
    simp only [block, rowRun]
    rw [run_unpack, run_packet (Φ := Φ) _ _ _ _ saved rfl, run_read, bind_assoc]
    simp only [pure_bind]
    congr 1
    funext y
    exact visit t (fun _ h => h) y
  | case a l r =>
    simp only [block, rowRun]
    rw [run_unpack, run_casePacket, bind_assoc]
    simp only [pure_bind]
    congr 1
    funext z
    cases z with
    | inl y => exact visit l (fun _ h => List.mem_append_left _ h) y
    | inr y => exact visit r (fun _ h => List.mem_append_right _ h) y
termination_by q.rank i
decreasing_by exact q.decreases hq edge

theorem continuation_carry_run_proof {L : LCtx (Ty Empty)}
    (q : Table Φ (β.snoc (packedExitType L)) K m) (hq : q.check = true) (ok : (carry q).check = true)
    (j : Fin (m + 1)) (a : Operand Φ (β.snoc (packedExitType L)) (q.types j))
    (env : BoundEnv Val β) (saved : Val (packedExitType L)) :
    run (continuation (carry q) j (carryEntry a) ok).2 (env.snoc saved) =
      run (q.toLetCase hq j a).2 (env.snoc saved) := by
  rw [continuation_run, emit_run]
  change ((pure saved >>= fun c => run a.2 (env.snoc saved) >>= fun x => pure (c, x)) >>=
    atRun (carry q) ok env j) = _
  rw [pure_bind, bind_assoc]
  simp only [pure_bind]
  congr 1
  funext x
  exact carry_at_run q hq ok env saved j x

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Open
