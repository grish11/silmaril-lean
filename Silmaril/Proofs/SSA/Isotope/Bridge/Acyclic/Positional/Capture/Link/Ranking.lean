module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link

open Region (packedExitType)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d n m : Nat} {β : BoundCtx τ d} {L K : LCtx τ}
  (p : Table Φ β L n) (q : Table Φ β K m)
  (j : Fin (m + 1)) (a : Operand Φ (β.snoc (packedExitType L)) (q.types j))

set_option backward.isDefEq.respectTransparency false

theorem block_left (i : Fin (n + 1)) :
    (table p q j a).block (leftIndex p q i) = castBlock (left_type p q i).symm (leftBlock p q i) := by
  simp only [table, leftIndex, Fin.addCases_left]

theorem block_handoff (i : Fin L.length) :
    (table p q j a).block (handoffIndex p q i) = castBlock (handoff_type p q i).symm (handoffBlock p q j a i) := by
  simp only [table, handoffIndex, Fin.addCases_left, Fin.addCases_right]

theorem block_right (i : Fin (m + 1)) :
    (table p q j a).block (rightIndex p q i) = castBlock (right_type p q i).symm (rightBlock p q i) := by
  simp only [table, rightIndex, Fin.addCases_right]

private theorem locals_block_cast {N : Nat} {R : Fin N → τ} {A B : τ} {X : LCtx τ}
    (h : A = B) (b : Block Φ β R X A) :
    (castBlock h b).locals = b.locals := by cases h; rfl

omit [HasTy Φ τ] [TypeFormers τ] in
private theorem locals_target_cast {N : Nat} {R : Fin N → τ} {A B : τ} {X : LCtx τ}
    (h : A = B) (t : Target R X A) :
    (castTarget h t).locals = t.locals := by cases h; rfl

private theorem left_edges (i : Fin (n + 1)) {t : Index p q}
    (h : t ∈ (table p q j a).localTargets (leftIndex p q i)) :
    (∃ k ∈ p.localTargets i, t = leftIndex p q k) ∨ ∃ k : Fin L.length, t = handoffIndex p q k := by
  unfold Table.localTargets at h
  rw [block_left, locals_block_cast, leftBlock] at h
  have visit {X : τ} (x : Target p.types L X) (hit : t ∈ (leftTarget p q x).locals) :
      (∃ k ∈ x.locals, t = leftIndex p q k) ∨ ∃ k : Fin L.length, t = handoffIndex p q k := by
    cases x with
    | «local» k =>
      rw [leftTarget, locals_target_cast] at hit
      change t ∈ [_] at hit
      rw [List.mem_singleton] at hit
      exact .inl ⟨k, by simp [Target.locals], hit⟩
    | exit exit =>
      rw [leftTarget, locals_target_cast] at hit
      change t ∈ [_] at hit
      rw [List.mem_singleton] at hit
      exact .inr ⟨_, hit⟩
  change (∃ k ∈ (p.block i).locals, t = leftIndex p q k) ∨ ∃ k : Fin L.length, t = handoffIndex p q k
  revert h
  cases p.block i with
  | jump op x => exact visit x
  | case op x y =>
    intro h
    change t ∈ _ ++ _ at h
    rw [List.mem_append] at h
    rcases h with hx | hy
    · exact (visit x hx).imp (fun ⟨k, h, eq⟩ => ⟨k, List.mem_append_left _ h, eq⟩) id
    · exact (visit y hy).imp (fun ⟨k, h, eq⟩ => ⟨k, List.mem_append_right _ h, eq⟩) id

private theorem right_edges (i : Fin (m + 1)) {t : Index p q}
    (h : t ∈ (table p q j a).localTargets (rightIndex p q i)) :
    ∃ k ∈ q.localTargets i, t = rightIndex p q k := by
  unfold Table.localTargets at h
  rw [block_right, locals_block_cast, rightBlock] at h
  have visit {X : τ} (x : Target q.types K X) (hit : t ∈ (rightTarget p q x).locals) :
      ∃ k ∈ x.locals, t = rightIndex p q k := by
    cases x with
    | «local» k =>
      rw [rightTarget, locals_target_cast] at hit
      change t ∈ [_] at hit
      rw [List.mem_singleton] at hit
      exact ⟨k, by simp [Target.locals], hit⟩
    | exit e => exact (List.not_mem_nil hit).elim
  change ∃ k ∈ (q.block i).locals, t = rightIndex p q k
  revert h
  cases q.block i with
  | jump op x => exact visit x
  | case op x y =>
    intro h
    change t ∈ _ ++ _ at h
    rw [List.mem_append] at h
    rcases h with hx | hy
    · obtain ⟨k, h, eq⟩ := visit x hx
      exact ⟨k, List.mem_append_left _ h, eq⟩
    · obtain ⟨k, h, eq⟩ := visit y hy
      exact ⟨k, List.mem_append_right _ h, eq⟩

private theorem handoff_edges (i : Fin L.length) {t : Index p q}
    (h : t ∈ (table p q j a).localTargets (handoffIndex p q i)) : t = rightIndex p q j := by
  unfold Table.localTargets at h
  rw [block_handoff, locals_block_cast] at h
  change t ∈ (castTarget (right_type p q j) (.local (rightIndex p q j) : Target (types p q) K _)).locals at h
  rw [locals_target_cast] at h
  exact List.mem_singleton.mp h

private theorem index_cases (i : Index p q) :
    (∃ k, i = leftIndex p q k) ∨ (∃ k, i = handoffIndex p q k) ∨ (∃ k, i = rightIndex p q k) :=
  Fin.addCases (m := n + 1 + L.length) (n := m + 1)
    (motive := fun i => (∃ k, i = leftIndex p q k) ∨ (∃ k, i = handoffIndex p q k) ∨ (∃ k, i = rightIndex p q k))
    (Fin.addCases (m := n + 1) (n := L.length) (fun k => .inl ⟨k, rfl⟩)
      (fun k => .inr (.inl ⟨k, rfl⟩)))
    (fun k => .inr (.inr ⟨k, rfl⟩)) i

private theorem exists_rank {N : Nat} (targets : Fin N → List (Fin N)) (ok : Rank.check targets = true) :
    ∃ rank : Fin N → Nat, (∀ i j, j ∈ targets i → rank j < rank i) ∧ ∀ i, rank i < N := by
  obtain ⟨live, rank, all, edge, bound⟩ := (Rank.checkFrom_iff targets (List.finRange N)).mp ok
  exact ⟨rank, fun i j h => (edge i j (all i (List.mem_finRange i)) h).2,
    fun i => bound i (all i (List.mem_finRange i))⟩

theorem check_proof (hp : p.check = true) (hq : q.check = true) : (table p q j a).check = true := by
  obtain ⟨rp, pd, pb⟩ := exists_rank p.localTargets hp
  obtain ⟨rq, qd, qb⟩ := exists_rank q.localTargets hq
  let rank : Index p q → Nat := Fin.addCases (m := n + 1 + L.length) (n := m + 1)
    (Fin.addCases (m := n + 1) (n := L.length) (fun i => rp i + (m + 1) + L.length) (fun _ => m + 1)) rq
  have lp (i : Fin (n + 1)) : rank (leftIndex p q i) = rp i + (m + 1) + L.length := by simp [rank, leftIndex]
  have lk (i : Fin L.length) : rank (handoffIndex p q i) = m + 1 := by simp [rank, handoffIndex]
  have lq (i : Fin (m + 1)) : rank (rightIndex p q i) = rq i := by simp [rank, rightIndex]
  apply Rank.check_complete _ rank
  · intro i t edge
    rcases index_cases p q i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rcases left_edges p q j a k edge with ⟨c, hit, rfl⟩ | ⟨c, rfl⟩
      · have dec := pd k c hit
        rw [lp, lp]
        omega
      · rw [lk, lp]
        have := c.isLt
        omega
    · obtain rfl := handoff_edges p q j a k edge
      rw [lq, lk]
      exact qb j
    · obtain ⟨c, hit, rfl⟩ := right_edges p q j a k edge
      rw [lq, lq]
      exact qd k c hit
  · intro i
    rcases index_cases p q i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [lp]
      have := pb k
      change rp k + (m + 1) + L.length < n + 1 + L.length + m + 1
      omega
    · rw [lk]
      change m + 1 < n + 1 + L.length + m + 1
      omega
    · rw [lq]
      have := qb k
      change rq k < n + 1 + L.length + m + 1
      omega

namespace Open

private theorem target_locals {N : Nat} {R : Fin N → τ} {X : LCtx τ} {A P : τ}
    (t : Target R X A) : (target (P := P) t).locals = t.locals := by
  cases t <;> rfl

private theorem block_locals {N : Nat} {R : Fin N → τ} {X : LCtx τ} {A P : τ}
    (b : Block Φ (β.snoc P) R X A) : (block b).locals = b.locals := by
  cases b with
  | jump a t => exact target_locals t
  | case a l r => exact congrArg₂ List.append (target_locals l) (target_locals r)

theorem carry_localTargets_proof {P : τ} (q : Table Φ (β.snoc P) K m) (i : Fin (m + 1)) :
    (carry q).localTargets i = q.localTargets i :=
  block_locals (q.block i)

theorem rename_check_proof {e : Nat} {δ : BoundCtx τ e} (r : BoundCtx.Renaming β δ)
    (q : Table Φ β K m) : (renameTable r q).check = q.check := by
  apply congrArg Rank.check
  funext i
  change (renameBlock r (q.block i)).locals = (q.block i).locals
  cases q.block i <;> rfl

end Open

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link
