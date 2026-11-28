module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Defs
public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Ranking

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link

open Region (packedExitType)
open LetCase.Structural.Reply (Γ₀ run)
open LetCase.LocallyNameless (Derivation)
open Isotope.Semantics (BoundEnv ProductModel CoproductModel EmptyModel)
open Reverse (Tree Edge tableTree blockTree targetTree tableProgram Program)
open Acyclic (Code)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

local notation "Val" => LetSeq.StraightLine.Structural.Value (α := Empty)
local notation "Trace" => LetSeq.StraightLine.Structural.Trace Empty
local notation "CTm" => LetCase.LocallyNameless.Tm Empty

variable {Φ : Type} [HasTy Φ (Ty Empty)] {d e f n m : Nat}
  {β : BoundCtx (Ty Empty) d} {γ : BoundCtx (Ty Empty) e} {δ : BoundCtx (Ty Empty) f}
  {A B : Ty Empty} {L K : List (Ty Empty)}

set_option backward.isDefEq.respectTransparency false

private def pull (r : BoundCtx.Renaming β γ) (env : BoundEnv Val γ) : BoundEnv Val β :=
  fun i => cast (congrArg Val (r.typed i)) (env (r.toFun i))

private theorem pull_up (r : BoundCtx.Renaming β γ) (env : BoundEnv Val γ) (v : Val A) :
    pull (r.up A) (env.snoc v) = (pull r env).snoc v := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem run_bv_cast {X Y : Ty Empty} {t : CTm Φ e} (eq : X = Y)
    (b : Derivation Φ Γ₀ γ t X) (env : BoundEnv Val γ) :
    run (eq ▸ b : Derivation Φ Γ₀ γ t Y) env =
      (run b env >>= fun x => pure (cast (congrArg Val eq) x)) := by
  cases eq
  exact (bind_pure _).symm

private theorem run_rename {t : CTm Φ d} (b : Derivation Φ Γ₀ β t A)
    (r : BoundCtx.Renaming β γ) (env : BoundEnv Val γ) :
    run (b.rename r) env = run b (pull r env) := by
  induction b generalizing e with
  | fv _ => rfl
  | bv =>
    simp only [Derivation.rename]
    rw [run_bv_cast]
    exact pure_bind _ _
  | op b ih => simp only [Derivation.rename, run, Derivation.denote] at *; rw [ih]
  | unit => rfl
  | let₁ b k ib ik =>
    change (run (b.rename r) env >>= fun x => run (k.rename (r.up _)) (env.snoc x)) =
      (run b (pull r env) >>= fun x => run k ((pull r env).snoc x))
    simp only [ib, ik, pull_up]
  | let₂ b k ib ik =>
    simp only [Derivation.rename, run, Derivation.denote] at *
    simp only [ib, ik, pull_up]
  | pair b k ib ik =>
    simp only [Derivation.rename, run, Derivation.denote] at *
    simp only [ib, ik]
  | inl b ih =>
    simp only [Derivation.rename, run, Derivation.denote] at *
    simp only [ih]
  | inr b ih =>
    simp only [Derivation.rename, run, Derivation.denote] at *
    simp only [ih]
  | case b l r ib il ir =>
    simp only [Derivation.rename, run, Derivation.denote] at *
    simp only [ib, il, ir, pull_up]
  | abort b ih =>
    simp only [Derivation.rename, run, Derivation.denote] at *
    simp only [ih]

private theorem pull_base (env : BoundEnv Val β) : pull (Scope.base : Scope β β).renaming env = env := rfl

private theorem pull_skip (s : Scope β γ) (env : BoundEnv Val γ) (v : Val A) :
    pull (s.skip A).renaming (env.snoc v) = pull s.renaming env := rfl

private def tagValue : (L : List (Ty Empty)) → (i : Nat) → At L i A → Val A → Val (packedExitType L)
  | [], _, h, _ => nomatch h
  | _X :: _, 0, h, v => .inl (cast (congrArg Val (Option.some.inj h).symm) v)
  | _ :: R, i + 1, h, v => .inr (tagValue R i h v)

private theorem run_tag (i : Nat) (h : At L i A) (a : Operand Φ β A) (env : BoundEnv Val β) :
    run (FiniteExit.tag L i h a).2 env = (run a.2 env >>= fun v => pure (tagValue L i h v)) := by
  induction L generalizing i with
  | nil => cases h
  | cons X R ih =>
    cases i with
    | zero =>
      have eq : X = A := Option.some.inj h
      subst X
      rfl
    | succ i =>
      change (run (FiniteExit.tag R i h a).2 env >>= fun v => pure (Sum.inr v)) = _
      rw [ih, bind_assoc]
      simp only [pure_bind, tagValue]

mutual

private def treeRun : {A : Ty Empty} → Tree Φ β L A → BoundEnv Val β → Val A →
    Trace Φ (Val (packedExitType L))
  | _, .jump a k, env, x => run a.2 (env.snoc x) >>= edgeRun k env
  | _, .case a l r, env, x => run a.2 (env.snoc x) >>= Sum.elim (edgeRun l env) (edgeRun r env)

private def edgeRun : {A : Ty Empty} → Edge Φ β L A → BoundEnv Val β → Val A →
    Trace Φ (Val (packedExitType L))
  | _, .exit (i := i) h, _, x => pure (tagValue L i h x)
  | _, .local b, env, x => treeRun b env x

end

private theorem run_case {X Y Z : Ty Empty} {t : CTm Φ e} {l r : CTm Φ (e + 1)}
    (b : Derivation Φ Γ₀ γ t (.coprod X Y))
    (dl : Derivation Φ Γ₀ (γ.snoc X) l Z) (dr : Derivation Φ Γ₀ (γ.snoc Y) r Z)
    (env : BoundEnv Val γ) :
    run (.case b dl dr) env =
      (run b env >>= Sum.elim (fun x => run dl (env.snoc x)) (fun y => run dr (env.snoc y))) := by
  unfold run
  simp only [Derivation.denote]
  congr 1
  funext x
  cases x <;> rfl

mutual

private theorem render_tree_run {A : Ty Empty} :
    (b : Tree Φ β L A) → ∀ {e : Nat} {γ : BoundCtx (Ty Empty) e}
    (s : Scope β γ) (env : BoundEnv Val γ) (x : Val A),
    run (b.render s).encode.toLetCase.2 (env.snoc x) = treeRun b (pull s.renaming env) x
  | .jump a k, _, _, s, env, x => by
    simp only [Tree.render, FiniteExit.encode, Code.toLetCase]
    change (run (s.operand a).2 (env.snoc x) >>= fun v => run (k.render (.skip s A)).encode.toLetCase.2
      ((env.snoc x).snoc v)) = _
    simp only [Scope.operand, run_rename, pull_up, treeRun]
    congr 1
    funext v
    exact (render_edge_run k (.skip s A) (env.snoc x) v).trans (by rw [pull_skip])
  | .case a l r, _, _, s, env, x => by
    simp only [Tree.render, FiniteExit.encode, Code.toLetCase]
    rw [run_case, treeRun]
    rw [show run (s.operand a).2 (env.snoc x) = run a.2 ((pull s.renaming env).snoc x) by
      simp only [Scope.operand, run_rename, pull_up]]
    congr 1
    funext v
    cases v with
    | inl u =>
      simp only [Sum.elim_inl]
      exact (render_edge_run l (.skip s A) (env.snoc x) u).trans (by rw [pull_skip])
    | inr u =>
      simp only [Sum.elim_inr]
      exact (render_edge_run r (.skip s A) (env.snoc x) u).trans (by rw [pull_skip])
termination_by structural b => b

private theorem render_edge_run {A : Ty Empty} :
    (b : Edge Φ β L A) → ∀ {e : Nat} {γ : BoundCtx (Ty Empty) e}
    (s : Scope β γ) (env : BoundEnv Val γ) (x : Val A),
    run (b.render s).encode.toLetCase.2 (env.snoc x) = edgeRun b (pull s.renaming env) x
  | .exit h, _, _, s, env, x => by
    change run (FiniteExit.tag L _ h ⟨.bv 0, .bv⟩).2 (env.snoc x) = _
    rw [run_tag]
    exact pure_bind _ _
  | .local b, _, _, s, env, x => render_tree_run b s env x
termination_by structural b => b

end

section Rows

variable {N : Nat} {R : Fin N → Ty Empty}

/-- Evaluate one row given the behavior at its written targets. -/
private def rowRun (b : Block Φ β R L A) (env : BoundEnv Val β)
    (go : ∀ {X}, Target R L X → Val X → Trace Φ (Val B)) (x : Val A) : Trace Φ (Val B) :=
  match b with
  | .jump a t => run a.2 (env.snoc x) >>= go t
  | .case a l r => run a.2 (env.snoc x) >>= Sum.elim (go l) (go r)

private theorem row_cast {A D : Ty Empty} (h : A = D) (b : Block Φ β R L A)
    (env : BoundEnv Val β) (go : ∀ {X}, Target R L X → Val X → Trace Φ (Val B)) (x : Val D) :
    rowRun (castBlock h b) env go x = rowRun b env go (cast (congrArg Val h.symm) x) := by
  cases h
  rfl

private theorem row_map {P : Fin n → Ty Empty} (b : Block Φ β R L A)
    (map : ∀ {X}, Target R L X → Target P K X)
    (env : BoundEnv Val β) (go : ∀ {X}, Target P K X → Val X → Trace Φ (Val B)) (x : Val A) :
    rowRun (mapTargets map b) env go x = rowRun b env (fun t => go (map t)) x := by
  cases b <;> rfl

private def targetRun {X : Ty Empty}
    (next : ∀ i, Val (R i) → Trace Φ (Val (packedExitType L))) :
    Target R L X → Val X → Trace Φ (Val (packedExitType L))
  | .local i, x => next i x
  | .exit (i := i) h, x => pure (tagValue L i h x)

private theorem target_cast {A D : Ty Empty} (h : A = D) (t : Target R L A)
    (next : ∀ i, Val (R i) → Trace Φ (Val (packedExitType L))) (x : Val D) :
    targetRun next (castTarget h t) x = targetRun next t (cast (congrArg Val h.symm) x) := by
  cases h
  rfl

private theorem row_tree (b : Block Φ β R L A) (env : BoundEnv Val β)
    (next : ∀ i, Tree Φ β L (R i)) (x : Val A) :
    treeRun (blockTree b (fun i _ => next i)) env x =
      rowRun b env (targetRun (fun i => treeRun (next i) env)) x := by
  have visit {X : Ty Empty} (t : Target R L X) (labels : List (Fin N)) (e : ∀ j ∈ t.locals, j ∈ labels) :
      edgeRun (targetTree t e (fun i _ => next i)) env =
        targetRun (fun i => treeRun (next i) env) t := by
    cases t <;> rfl
  cases b with
  | jump a t =>
    exact congrArg (fun k => run a.2 (env.snoc x) >>= k) (visit t t.locals (fun _ h => h))
  | case a l r =>
    exact congrArg₂ (fun kl kr => run a.2 (env.snoc x) >>= Sum.elim kl kr)
      (visit l (l.locals ++ r.locals) (fun _ h => List.mem_append_left _ h))
      (visit r (l.locals ++ r.locals) (fun _ h => List.mem_append_right _ h))

private theorem row_congr (b : Block Φ β R L A) (env : BoundEnv Val β) (x : Val A)
    (go next : ∀ {X}, Target R L X → Val X → Trace Φ (Val B))
    (same : ∀ {X} (t : Target R L X), (∀ i ∈ t.locals, i ∈ b.locals) → go t = next t) :
    rowRun b env go x = rowRun b env next x := by
  cases b with
  | jump a t => rw [rowRun, rowRun, same t (fun _ h => h)]
  | case a l r =>
    rw [rowRun, rowRun, same l (fun _ h => List.mem_append_left _ h),
      same r (fun _ h => List.mem_append_right _ h)]

private theorem row_bind (b : Block Φ β R L A) (env : BoundEnv Val β) (x : Val A)
    (go : ∀ {X}, Target R L X → Val X → Trace Φ (Val (packedExitType L)))
    (k : Val (packedExitType L) → Trace Φ (Val B)) :
    (rowRun b env go x >>= k) = rowRun b env (fun t v => go t v >>= k) x := by
  cases b with
  | jump a t => exact bind_assoc _ _ _
  | case a l r =>
    simp only [rowRun, bind_assoc]
    congr 1
    funext v
    cases v <;> rfl

end Rows

private def atRun (p : Table Φ β L n) (hp : p.check = true) (env : BoundEnv Val β)
    (i : Fin (n + 1)) : Val (p.types i) → Trace Φ (Val (packedExitType L)) :=
  treeRun (tableTree p hp i) env

private theorem atRun_row (p : Table Φ β L n) (hp : p.check = true) (env : BoundEnv Val β)
    (i : Fin (n + 1)) (x : Val (p.types i)) :
    atRun p hp env i x = rowRun (p.block i) env (targetRun (atRun p hp env)) x := by
  unfold atRun
  rw [tableTree.eq_def, row_tree]

private theorem emit_run (p : Table Φ β L n) (hp : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) (env : BoundEnv Val β) :
    run (p.toLetCase hp i a).2 env = (run a.2 env >>= atRun p hp env i) := by
  rw [Table.toLetCase, ← Reverse.tableProgram_render]
  change (run a.2 env >>= fun x => run ((tableTree p hp i).render .base).encode.toLetCase.2 (env.snoc x)) = _
  congr 1
  funext x
  exact render_tree_run _ .base env x

private theorem handoff_run (a : Operand Φ (β.snoc (packedExitType L)) B)
    (i : Fin L.length) (env : BoundEnv Val β) (x : Val (L.get i)) :
    run (handoffOperand a i).2 (env.snoc x) = run a.2 (env.snoc (tagValue L i (at_get i) x)) := by
  unfold handoffOperand
  change (run (FiniteExit.tag L i.val (at_get i) ⟨.bv 0, .bv⟩).2 (env.snoc x) >>= fun z =>
    run (a.2.rename ((BoundCtx.Renaming.succ β (L.get i)).up (packedExitType L))) ((env.snoc x).snoc z)) = _
  rw [run_tag, bind_assoc]
  simp only [run_rename, pull_up]
  rw [show run (Derivation.bv (ι := 0) : Derivation Φ Γ₀ (β.snoc (L.get i)) (.bv 0) (L.get i))
      (env.snoc x) = pure x from rfl, pure_bind]
  rw [pure_bind]
  rfl

private theorem cast_round {X Y : Ty Empty} (h : X = Y) (x : Val X) :
    cast (congrArg Val h.symm) (cast (congrArg Val h) x) = x := by
  cases h
  rfl

private theorem cast_chain {X Y Z : Ty Empty} (h : X = Y) (k : Y = Z) (x : Val Z) :
    cast (congrArg Val (h.trans k).symm) x =
      cast (congrArg Val h.symm) (cast (congrArg Val k.symm) x) := by
  cases h
  cases k
  rfl

private theorem tagValue_cast (h : At L n A) (x : Val A) :
    tagValue L n (at_get ⟨n, at_lt h⟩) (cast (congrArg Val (at_eq h).symm) x) =
      tagValue L n h x := by
  induction L generalizing n with
  | nil => cases h
  | cons X R ih =>
    cases n with
    | zero =>
      have eq : X = A := Option.some.inj h
      subst X
      rfl
    | succ i =>
      change Sum.inr (tagValue R i (at_get ⟨i, at_lt (L := R) h⟩)
        (cast (congrArg Val (at_eq (L := R) h).symm) x)) = Sum.inr (tagValue R i h x)
      rw [ih h]

section Link

variable (p : Table Φ β L n) (q : Table Φ β K m) (hp : p.check = true) (hq : q.check = true)
  (j : Fin (m + 1)) (a : Operand Φ (β.snoc (packedExitType L)) (q.types j))
  (env : BoundEnv Val β)

private abbrev linked := table p q j a
private abbrev linkedCheck := check_proof p q j a hp hq

private theorem right_run (i : Fin (m + 1)) (x : Val (q.types i)) :
    atRun (linked p q j a) (linkedCheck p q hp hq j a) env (rightIndex p q i)
      (cast (congrArg Val (right_type p q i).symm) x) = atRun q hq env i x := by
  rw [atRun_row (linked p q j a), atRun_row q, block_right,
    row_cast (right_type p q i).symm, cast_round (right_type p q i).symm, rightBlock, row_map]
  apply row_congr
  intro X t visit
  funext v
  cases t with
  | «local» k =>
    have edge : k ∈ q.localTargets i := visit k (by simp [Target.locals])
    rw [rightTarget, target_cast]
    exact right_run k v
  | exit h => rfl
termination_by q.rank i
decreasing_by exact q.decreases hq edge

private theorem handoff_at (i : Fin L.length) (x : Val (L.get i)) :
    atRun (linked p q j a) (linkedCheck p q hp hq j a) env (handoffIndex p q i)
      (cast (congrArg Val (handoff_type p q i).symm) x) =
    (run a.2 (env.snoc (tagValue L i (at_get i) x)) >>= atRun q hq env j) := by
  rw [atRun_row, block_handoff, row_cast (handoff_type p q i).symm, cast_round (handoff_type p q i).symm, handoffBlock, rowRun, handoff_run]
  congr 1
  funext v
  rw [target_cast]
  exact right_run p q hp hq j a env j v

private theorem left_run (i : Fin (n + 1)) (x : Val (p.types i)) :
    atRun (linked p q j a) (linkedCheck p q hp hq j a) env (leftIndex p q i)
      (cast (congrArg Val (left_type p q i).symm) x) =
    (atRun p hp env i x >>= fun z => run a.2 (env.snoc z) >>= atRun q hq env j) := by
  rw [atRun_row (linked p q j a), atRun_row p, block_left,
    row_cast (left_type p q i).symm, cast_round (left_type p q i).symm, leftBlock, row_map, row_bind]
  apply row_congr
  intro X t visit
  funext v
  cases t with
  | «local» k =>
    have edge : k ∈ p.localTargets i := visit k (by simp [Target.locals])
    rw [leftTarget, target_cast]
    exact left_run k v
  | @exit i X h =>
    rw [leftTarget, target_cast]
    let k : Fin L.length := ⟨i, at_lt h⟩
    let y := cast (congrArg Val (at_eq h).symm) v
    have eq : cast (congrArg Val ((handoff_type p q k).trans (at_eq h)).symm) v =
        cast (congrArg Val (handoff_type p q k).symm) y := cast_chain (handoff_type p q k) (at_eq h) v
    rw [eq]
    change atRun (linked p q j a) (linkedCheck p q hp hq j a) env (handoffIndex p q k)
      (cast (congrArg Val (handoff_type p q k).symm) y) = _
    rw [handoff_at p q hp hq j a env k y, targetRun, pure_bind]
    rw [tagValue_cast h v]
termination_by p.rank i
decreasing_by exact p.decreases hp edge

private theorem continuation_run (z : Val (packedExitType L)) :
    run (continuation q j a hq).2 (env.snoc z) =
      (run a.2 (env.snoc z) >>= atRun q hq env j) := by
  change (run a.2 (env.snoc z) >>= fun x =>
    run ((tableTree q hq j).render (.skip .base (packedExitType L))).encode.toLetCase.2 ((env.snoc z).snoc x)) = _
  congr 1
  funext x
  rw [render_tree_run, pull_skip, pull_base]
  rfl

private theorem cast_entry_run {X Y : Ty Empty} (h : X = Y) (start : Operand Φ β X) :
    run (cast (congrArg (Operand Φ β) h) start).2 env =
      (run start.2 env >>= fun v => pure (cast (congrArg Val h) v)) := by
  cases h
  exact (bind_pure _).symm

theorem serial_run_proof (i : Fin (n + 1)) (start : Operand Φ β (p.types i))
    (ok : (table p q j a).check = true) :
    run ((table p q j a).toLetCase ok (leftIndex p q i) (entry p q j a i start)).2 env =
      run (bind (p.toLetCase hp i start) (continuation q j a hq)).2 env := by
  rw [emit_run]
  change (run (cast (congrArg (Operand Φ β) (left_type p q i).symm) start).2 env >>=
    atRun (linked p q j a) (linkedCheck p q hp hq j a) env (leftIndex p q i)) = _
  rw [cast_entry_run env (left_type p q i).symm, bind_assoc]
  simp only [pure_bind]
  simp only [left_run p q hp hq j a env i]
  change _ = (run (p.toLetCase hp i start).2 env >>= fun z => run (continuation q j a hq).2 (env.snoc z))
  simp only [continuation_run, emit_run, bind_assoc]

end Link

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link
