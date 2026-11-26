module

public import Silmaril.Proofs.SSA.PEG.Rules.Local

public section

namespace Silmaril.SSA.PEG.Rules.Proofs

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {out : Ty Data} {n l : Nat}
variable {g : Graph P params results n l} {m : Interpretation.{u,v,x} P}
variable {values : g.Valuation m} {env : Tuple m.Value params}

variable (solves : g.Solves m env values)

section Phi
variable {r yes no : Ref g.sort out} {cond : Ref g.sort .bool}
variable (node : HasNode r .phi (.cons cond (.cons yes (.cons no .nil))))

include solves node in
theorem phi_true (guard : ∀ i, readRef values cond i = some ⟨true⟩) : StreamEq values r yes := by
  intro i
  rw [phi_at solves node i, guard i]
  rfl

include solves node in
theorem phi_false (guard : ∀ i, readRef values cond i = some ⟨false⟩) : StreamEq values r no := by
  intro i
  rw [phi_at solves node i, guard i]
  rfl

include solves in
theorem phi_same_of_defined {a : Ref g.sort out}
    (node : HasNode r .phi (.cons cond (.cons a (.cons a .nil))))
    (defined : ∀ i, (readRef values cond i).isSome) : StreamEq values r a := by
  intro i
  rw [phi_at solves node i]
  have safe := defined i
  cases h : readRef values cond i with
  | none =>
    rw [h] at safe
    cases safe
  | some flag =>
    cases flag with
    | up b => cases b <;> rfl

include solves in
theorem phi_nested_true {r' inner t f fallback : Ref g.sort out}
    (outer : HasNode r .phi (.cons cond (.cons inner (.cons fallback .nil))))
    (branch : HasNode inner .phi (.cons cond (.cons t (.cons f .nil))))
    (simple : HasNode r' .phi (.cons cond (.cons t (.cons fallback .nil)))) : StreamEq values r r' := by
  intro i
  rw [phi_at solves outer i, phi_at solves simple i, phi_at solves branch i]
  cases readRef values cond i with
  | none => rfl
  | some flag =>
    cases flag with
    | up b => cases b <;> rfl

end Phi

private theorem monotonize_zero {α : Type x} (stream : Nat → Option α) :
    monotonize stream 0 = stream 0 := by
  have earlierDefined : ∀ j : Fin 0, (stream j.val).isSome := fun j => j.elim0
  simp only [monotonize, ite_eq_left earlierDefined]

private theorem monotonize_const {α : Type x} (a : Option α) (k : Nat) :
    monotonize (fun _ => a) k = a := by
  cases a with
  | none => unfold monotonize; split <;> rfl
  | some value => exact (monotonize_eq_some_iff _ _ _).2 ⟨rfl, fun _ _ => rfl⟩

include solves in
theorem eval_zero {r source : Ref g.sort out} {count : Ref g.sort .count} {loop : Fin l}
    (node : HasNode r (.eval loop) (.cons source (.cons count .nil))) {i : Index l}
    (atZero : readRef values count i = some ⟨0⟩) :
    readRef values r i = readRef values source (i.set loop 0) := by
  rw [eval_at solves node i, atZero]
  exact monotonize_zero (fun j => readRef values source (i.set loop j))

include solves in
theorem eval_zero_theta {r r' theta initial feedback : Ref g.sort out} {count : Ref g.sort .count}
    {loop : Fin l} (evalTheta : HasNode r (.eval loop) (.cons theta (.cons count .nil)))
    (thetaNode : HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (evalInitial : HasNode r' (.eval loop) (.cons initial (.cons count .nil)))
    (zero : ∀ i, readRef values count i = some ⟨0⟩) : StreamEq values r r' := by
  intro i
  calc
    readRef values r i = readRef values theta (i.set loop 0) := eval_zero solves evalTheta (zero i)
    _ = readRef values initial (i.set loop 0) := theta_zero solves thetaNode (set_at i loop 0)
    _ = readRef values r' i := (eval_zero solves evalInitial (zero i)).symm

include solves in
theorem eval_invariant {r source : Ref g.sort out} {count : Ref g.sort .count} {loop : Fin l}
    (node : HasNode r (.eval loop) (.cons source (.cons count .nil)))
    (invariant : Invariant values loop source) (defined : ∀ i, (readRef values count i).isSome) :
    StreamEq values r source := by
  intro i
  have samples : (fun k => readRef values source (i.set loop k)) = fun _ => readRef values source i :=
    funext fun k => invariant _ _ (set_agree i loop k)
  rw [eval_at solves node i, samples]
  have safe := defined i
  cases h : readRef values count i with
  | none =>
    rw [h] at safe
    cases safe
  | some k => exact monotonize_const _ k.down

include solves in
theorem theta_self {r initial feedback : Ref g.sort out} {loop : Fin l}
    (node : HasNode r (.theta loop) (.cons initial (.cons feedback .nil)))
    (cycle : StreamEq values feedback r) (invariant : Invariant values loop initial) :
    StreamEq values r initial := by
  intro i
  have same : ∀ k, readRef values r (i.set loop k) = readRef values initial i := by
    intro k
    induction k with
    | zero => exact (theta_zero solves node (set_at i loop 0)).trans (invariant _ _ (set_agree i loop 0))
    | succ k ih =>
      rw [theta_succ solves node (set_at i loop (k + 1)), cycle _, set_twice]
      exact ih
  simpa only [set_current] using same (i loop)

include solves in
theorem pass_zero {r : Ref g.sort .count} {cond : Ref g.sort .bool} {loop : Fin l}
    (node : HasNode r (.pass loop) (.cons cond .nil)) {i : Index l}
    (first : readRef values cond (i.set loop 0) = some ⟨true⟩) : readRef values r i = some ⟨0⟩ := by
  rw [pass_at solves node i]
  have least : firstTrue (fun j => (readRef values cond (i.set loop j)).map ULift.down) = some 0 :=
    (firstTrue_eq_some_iff _ _).2 ⟨by rw [monotonize_zero, first]; rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  rw [least]
  rfl

private def prependFalse (stream : Nat → Option Bool) : Nat → Option Bool
  | 0 => some false
  | k + 1 => stream k

private theorem monotonize_prepend_false (stream : Nat → Option Bool) (k : Nat) :
    monotonize (prependFalse stream) (k + 1) = monotonize stream k := by
  have earlierDefined : (∀ j : Fin (k + 1), (prependFalse stream j.val).isSome) ↔
      (∀ j : Fin k, (stream j.val).isSome) :=
    ⟨fun h j => h j.succ, fun h j => Fin.cases rfl (fun p => h p) j⟩
  simp only [monotonize, earlierDefined]
  rfl

private theorem firstTrue_prepend_false (stream : Nat → Option Bool) :
    firstTrue (prependFalse stream) = (firstTrue stream).map Nat.succ := by
  cases h : firstTrue stream with
  | none =>
    apply (firstTrue_eq_none_iff _).2
    intro k
    cases k with
    | zero => simp [monotonize_zero, prependFalse]
    | succ k =>
      rw [monotonize_prepend_false]
      exact (firstTrue_eq_none_iff _).1 h k
  | some k =>
    have least := (firstTrue_eq_some_iff _ _).1 h
    apply (firstTrue_eq_some_iff _ _).2
    refine ⟨(monotonize_prepend_false stream k).trans least.1, ?_⟩
    intro j lt
    cases j with
    | zero => simp [monotonize_zero, prependFalse]
    | succ j =>
      rw [monotonize_prepend_false]
      exact least.2 j (Nat.lt_of_succ_lt_succ lt)

include solves in
private theorem pass_shift_of_false {r backPass : Ref g.sort .count}
    {predicate suffix : Ref g.sort .bool} {loop : Fin l}
    (passMain : HasNode r (.pass loop) (.cons predicate .nil))
    (passSuffix : HasNode backPass (.pass loop) (.cons suffix .nil)) {i : Index l}
    (first : readRef values predicate (i.set loop 0) = some ⟨false⟩)
    (samples : ∀ k, readRef values predicate (i.set loop (k + 1)) =
      readRef values suffix (i.set loop k)) :
    readRef values r i = (readRef values backPass i).map (fun k => ⟨k.down + 1⟩) := by
  let stream (k : Nat) := (readRef values suffix (i.set loop k)).map ULift.down
  have shifted : (fun k => (readRef values predicate (i.set loop k)).map ULift.down) = prependFalse stream := by
    funext k
    cases k with
    | zero => rw [first]; rfl
    | succ k => exact congrArg (Option.map ULift.down) (samples k)
  rw [pass_at solves passMain i, pass_at solves passSuffix i, shifted, firstTrue_prepend_false]
  change ((firstTrue stream).map Nat.succ).map ULift.up =
    ((firstTrue stream).map ULift.up).map (fun k => ⟨k.down + 1⟩)
  cases firstTrue stream <;> rfl

include solves in
theorem pass_peel {r backPass : Ref g.sort .count} {predicate suffix : Ref g.sort .bool}
    {loop : Fin l} (passMain : HasNode r (.pass loop) (.cons predicate .nil))
    (passSuffix : HasNode backPass (.pass loop) (.cons suffix .nil)) {i : Index l}
    (samples : ∀ k, readRef values predicate (i.set loop (k + 1)) = readRef values suffix (i.set loop k)) :
    readRef values r i = (readRef values predicate (i.set loop 0)).elim none
      (fun flag => if flag.down then some ⟨0⟩ else (readRef values backPass i).map (fun k => ⟨k.down + 1⟩)) := by
  cases head : readRef values predicate (i.set loop 0) with
  | none =>
    have blocked : firstTrue (fun k => (readRef values predicate (i.set loop k)).map ULift.down) = none := by
      apply (firstTrue_eq_none_iff _).2
      intro k result
      have hit := (monotonize_eq_some_iff _ _ _).1 result
      cases k with
      | zero =>
        have atZero := hit.1
        rw [head] at atZero
        cases atZero
      | succ k =>
        have earlier := hit.2 0 (Nat.zero_lt_succ k)
        rw [head] at earlier
        cases earlier
    rw [pass_at solves passMain i, blocked]
    rfl
  | some flag =>
    cases flag with
    | up flag =>
      cases flag with
      | false => exact pass_shift_of_false solves passMain passSuffix head samples
      | true => exact pass_zero solves passMain head

include solves in
theorem pass_peel_phi {r r' backPass shifted countZero : Ref g.sort .count}
    {predicate suffix first : Ref g.sort .bool} {loop : Fin l} {op : P [.count] .count}
    (passMain : HasNode r (.pass loop) (.cons predicate .nil))
    (passSuffix : HasNode backPass (.pass loop) (.cons suffix .nil))
    (sampleFirst : HasNode first (.eval loop) (.cons predicate (.cons countZero .nil)))
    (succNode : HasNode shifted (.op op) (.cons backPass .nil))
    (select : HasNode r' .phi (.cons first (.cons countZero (.cons shifted .nil))))
    (zero : ∀ i, readRef values countZero i = some ⟨0⟩)
    (successor : ∀ k : m.Value .count, m.run op (.cons k .nil) = some ⟨k.down + 1⟩)
    (samples : ∀ (i : Index l) k, readRef values predicate (i.set loop (k + 1)) =
      readRef values suffix (i.set loop k)) : StreamEq values r r' := by
  intro i
  rw [pass_peel solves passMain passSuffix (samples i), phi_at solves select i,
    eval_zero solves sampleFirst (zero i), zero i, unary_at solves succNode i]
  cases readRef values predicate (i.set loop 0) with
  | none => rfl
  | some flag =>
    cases flag with
    | up flag =>
      cases flag with
      | true => rfl
      | false =>
        cases readRef values backPass i with
        | none => rfl
        | some k => exact (successor k).symm

include solves in
theorem pass_theta_false {r backPass : Ref g.sort .count} {theta initial feedback : Ref g.sort .bool}
    {loop : Fin l} (passTheta : HasNode r (.pass loop) (.cons theta .nil))
    (thetaNode : HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (passFeedback : HasNode backPass (.pass loop) (.cons feedback .nil))
    (initialFalse : ∀ i : Index l, readRef values initial (i.set loop 0) = some ⟨false⟩) (i : Index l) :
    readRef values r i = (readRef values backPass i).map (fun k => ⟨k.down + 1⟩) := by
  apply pass_shift_of_false solves passTheta passFeedback
  · exact (theta_zero solves thetaNode (set_at i loop 0)).trans (initialFalse i)
  · intro k
    rw [theta_succ solves thetaNode (set_at i loop (k + 1)), set_twice]

include solves in
theorem pass_theta_false_succ {r r' backPass : Ref g.sort .count}
    {theta initial feedback : Ref g.sort .bool} {loop : Fin l} {op : P [.count] .count}
    (passTheta : HasNode r (.pass loop) (.cons theta .nil))
    (thetaNode : HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (passFeedback : HasNode backPass (.pass loop) (.cons feedback .nil))
    (succNode : HasNode r' (.op op) (.cons backPass .nil))
    (initialFalse : ∀ i : Index l, readRef values initial (i.set loop 0) = some ⟨false⟩)
    (successor : ∀ k : m.Value .count, m.run op (.cons k .nil) = some ⟨k.down + 1⟩) :
    StreamEq values r r' := by
  intro i
  rw [pass_theta_false solves passTheta thetaNode passFeedback initialFalse i, unary_at solves succNode i]
  cases readRef values backPass i with
  | none => rfl
  | some k => exact (successor k).symm

end Silmaril.SSA.PEG.Rules.Proofs
