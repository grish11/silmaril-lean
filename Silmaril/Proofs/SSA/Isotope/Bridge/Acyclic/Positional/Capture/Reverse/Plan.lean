module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

set_option backward.isDefEq.respectTransparency false

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d : Nat} {β : BoundCtx τ d} {L : LCtx τ} {A B : τ} {R S : List τ}

/-- Read a plan in allocation order. Each local transfer enters the plan
that existed when its source block was allocated. -/
private def Plan.unfoldAt : {R : List τ} → Plan Φ β L R → (i : Fin R.length) →
    {m : Nat} → {γ : BoundCtx τ m} → Scope β γ → FiniteExit Φ L (γ.snoc (R.get i))
  | [], .empty, i, _, _, _ => i.elim0
  | A :: R, .push p b, i, _, γ, s =>
    Fin.cases (motive := fun j => FiniteExit Φ L (γ.snoc ((A :: R).get j)))
      (b.compile s (fun j _ _ _ t => p.unfoldAt j t)) (fun j => p.unfoldAt j s) i

private def unfoldTarget (p : Plan Φ β L R) (t : Target R.get L A)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) : FiniteExit Φ L (γ.snoc A) :=
  match t with
  | .local i => p.unfoldAt i s
  | .exit h => .br h ⟨.bv 0, .bv⟩

omit [TypeFormers τ] in
private theorem shiftTarget_locals (t : Target R.get L A) :
    (shiftTarget B t).locals = t.locals.map Fin.succ := by
  cases t <;> rfl

private theorem shiftBlock_locals (b : Block Φ β R.get L A) :
    (shiftBlock B b).locals = b.locals.map Fin.succ := by
  cases b <;> simp [shiftBlock, Block.locals, shiftTarget_locals, List.map_append]

private theorem blocks_forward (p : Plan Φ β L R) (i j : Fin R.length)
    (edge : j ∈ (p.blockAt i).locals) : i.val < j.val := by
  induction p with
  | empty => exact i.elim0
  | push p b ih =>
    revert edge
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Plan.blockAt, Fin.cases_zero, shiftBlock_locals]
      intro edge
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp edge
      exact Nat.zero_lt_succ k.val
    · simp only [Plan.blockAt, Fin.cases_succ, shiftBlock_locals]
      intro edge
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp edge
      exact Nat.succ_lt_succ (ih i k hk)

theorem plan_check_proof (p : Plan Φ β L (A :: R)) : p.toTable.check = true := by
  apply Rank.check_complete p.toTable.localTargets (fun i => R.length - i.val)
  · intro i j edge
    have h := blocks_forward p i j edge
    have hi := i.isLt
    have hj := j.isLt
    omega
  · intro i
    omega

private theorem shiftBlock_compile (b : Block Φ β R.get L A)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ)
    (next : LocalContinuations β (B :: R).get L Φ (shiftBlock B b).locals) :
    (shiftBlock B b).compile s next =
      b.compile s (fun j edge _ _ t => next j.succ
        (by rw [shiftBlock_locals]; exact List.mem_map_of_mem edge) t) := by
  cases b with
  | jump op t => cases t <;> rfl
  | case op l r => cases l <;> cases r <;> rfl

private theorem unfold_step (p : Plan Φ β L R) (i : Fin R.length)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    p.unfoldAt i s = (p.blockAt i).compile s (fun j _ _ _ t => p.unfoldAt j t) := by
  induction p with
  | empty => exact i.elim0
  | @push R B p b ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change b.compile s _ = (shiftBlock B b).compile s _
      rw [shiftBlock_compile]
      rfl
    · change p.unfoldAt i s = (shiftBlock B (p.blockAt i)).compile s _
      rw [shiftBlock_compile]
      exact ih i

private theorem plan_compileAt (p : Plan Φ β L (A :: R)) (ok : p.toTable.check = true)
    (i : Fin (R.length + 1)) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    p.toTable.compileAt ok i s = p.unfoldAt i s := by
  rw [Table.compileAt.eq_def, unfold_step p i s]
  change (p.blockAt i).compile s _ = (p.blockAt i).compile s _
  congr 1
  funext j edge m' γ' t
  exact plan_compileAt p ok j t
termination_by p.toTable.rank i
decreasing_by exact p.toTable.decreases ok edge

private theorem unfoldTarget_push (p : Plan Φ β L R) (b : Block Φ β R.get L B)
    (t : Target R.get L A) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    unfoldTarget (p.push b) (shiftTarget B t) s = unfoldTarget p t s := by
  cases t <;> rfl

private theorem Extension.unfoldTarget {p : Plan Φ β L R} {q : Plan Φ β L S}
    (e : Extension p q) (t : Target R.get L A) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    unfoldTarget q (e.target t) s = unfoldTarget p t s := by
  induction e with
  | same => rfl
  | push prev b ih =>
    exact (unfoldTarget_push _ b (prev.target t) s).trans ih

private theorem unfold_jump (p : Plan Φ β L R) {B : τ}
    (op : Operand Φ (β.snoc A) B) (k : Target R.get L B)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    (p.push (.jump op k)).unfoldAt 0 s = .join (.br (s.operand op)) (unfoldTarget p k (.skip s A)) := by
  cases k <;> rfl

private theorem unfold_case (p : Plan Φ β L R) {B D : τ}
    (op : Operand Φ (β.snoc A) (coprod B D)) (l : Target R.get L B) (r : Target R.get L D)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    (p.push (.case op l r)).unfoldAt 0 s =
      .case (s.operand op) (unfoldTarget p l (.skip s A)) (unfoldTarget p r (.skip s A)) := by
  cases l <;> cases r <;> rfl

mutual

private theorem tree_build : ∀ {A : τ} (t : Tree Φ β L A) {R : List τ} (p : Plan Φ β L R)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ),
    (t.build p).plan.unfoldAt 0 s = t.render s
  | _, .jump op k, _, p, _, _, s => by
    change ((k.build p).plan.push (.jump op (k.build p).target)).unfoldAt 0 s = _
    rw [unfold_jump, edge_build k p]
    rfl
  | _, .case op l r, _, p, _, _, s => by
    let b := l.build p
    let c := r.build b.plan
    change (c.plan.push (.case op (c.extension.target b.target) c.target)).unfoldAt 0 s = _
    rw [unfold_case, c.extension.unfoldTarget, edge_build l p, edge_build r b.plan]
    rfl
termination_by structural _ t => t

private theorem edge_build : ∀ {A : τ} (k : Edge Φ β L A) {R : List τ} (p : Plan Φ β L R)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ),
    unfoldTarget (k.build p).plan (k.build p).target s = k.render s
  | _, .exit _, _, _, _, _, _ => rfl
  | _, .local t, _, p, _, _, s => tree_build t p s
termination_by structural _ k => k

end

theorem program_toFiniteExit_proof (p : Program Φ β L) (ok : p.toTable.check = true) :
    p.toTable.toFiniteExit ok 0 p.entry = p.toFiniteExit := by
  unfold Program.toTable Table.toFiniteExit Program.toFiniteExit
  exact congrArg (FiniteExit.join (.br p.entry))
    ((plan_compileAt p.build.plan ok 0 .base).trans (tree_build p.body Plan.empty .base))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
