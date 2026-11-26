module

public import Silmaril.SSA.PEG.Rules.Defs

public section

namespace Silmaril.SSA.PEG.Rules.Proofs

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results ins : List (Ty Data)} {out : Ty Data} {n l : Nat}
variable {g : Graph P params results n l} {m : Interpretation.{u,v,x} P}
variable {values : g.Valuation m} {env : Tuple m.Value params}

@[simp] theorem set_at (i : Index l) (loop : Fin l) (k : Nat) : i.set loop k loop = k := by
  simp [Index.set]

theorem set_agree (i : Index l) (loop : Fin l) (k : Nat) : AgreeExcept loop (i.set loop k) i := by
  intro j ne
  simp [Index.set, ne]

theorem set_current (i : Index l) (loop : Fin l) : i.set loop (i loop) = i := by
  funext j
  by_cases h : j = loop <;> simp [Index.set, h]

theorem set_twice (i : Index l) (loop : Fin l) (a b : Nat) : (i.set loop a).set loop b = i.set loop b := by
  funext j
  by_cases h : j = loop <;> simp [Index.set, h]

theorem set_congr {loop : Fin l} {i j : Index l} (same : AgreeExcept loop i j) (other : Fin l)
    (k : Nat) : AgreeExcept loop (i.set other k) (j.set other k) := by
  intro p ne
  by_cases h : p = other <;> simp [Index.set, h, same p ne]

theorem set_eq_of_agree {loop : Fin l} {i j : Index l} (same : AgreeExcept loop i j) (k : Nat) :
    i.set loop k = j.set loop k := by
  funext p
  by_cases h : p = loop
  · simp [Index.set, h]
  · simpa [Index.set, h] using same p h

theorem readRef_heq (r : Ref g.sort out) (i : Index l) :
    HEq (readRef values r i) (values (r.id, i)) := by
  cases r with
  | mk a typed =>
    cases typed
    rfl

theorem streamEq_iff_vertex (a b : Ref g.sort out) :
    StreamEq values a b ↔ (g.sort a.id = g.sort b.id ∧ ∀ i, HEq (values (a.id, i)) (values (b.id, i))) :=
  ⟨fun eq => ⟨a.typed.trans b.typed.symm, fun i =>
    (readRef_heq a i).symm.trans ((heq_of_eq (eq i)).trans (readRef_heq b i))⟩,
   fun eq i => eq_of_heq ((readRef_heq a i).trans ((eq.2 i).trans (readRef_heq b i).symm))⟩

theorem at_label (solves : g.Solves m env values) {r : Ref g.sort out}
    {label : Label P params (Fin l) ins out} {args : Tuple (Ref g.sort) ins}
    (node : HasNode r label args) (i : Index l) :
    readRef values r i = label.interpret m env i
      (fun slot j _ => readRef values (args.get (portAt ins slot)) j) := by
  cases r with
  | mk a typed =>
    cases typed
    have row : g.node a = Node.ofLabel label args := eq_of_heq node
    have eq := solves (a, i)
    change values (a, i) = (g.node a).label.interpret m env i
      (fun s j _ => readRef values ((g.node a).arg s) j) at eq
    rw [row] at eq
    exact eq

theorem phi_at (solves : g.Solves m env values) {r yes no : Ref g.sort out}
    {cond : Ref g.sort .bool} (node : HasNode r .phi (.cons cond (.cons yes (.cons no .nil))))
    (i : Index l) : readRef values r i = (readRef values cond i).elim none
      (fun flag => if flag.down then readRef values yes i else readRef values no i) :=
  at_label solves node i

theorem interpret_theta (m : Interpretation.{u,v,x} P) (env : Tuple m.Value params)
    (i : Index l) (loop : Fin l)
    (read : ∀ s : Fin ([out, out] : List (Ty Data)).length,
      Index l → Option (m.Value ([out, out] : List (Ty Data))[s])) :
    (Label.theta loop).interpret m env i (fun s j _ => read s j) =
      match i loop with
      | 0 => read 0 i
      | k + 1 => read 1 (i.set loop k) := by
  simp only [Label.interpret]
  split
  · rename_i h
    rw [h]
  · rename_i k h
    rw [h]

theorem theta_zero (solves : g.Solves m env values) {r initial feedback : Ref g.sort out}
    {loop : Fin l} (node : HasNode r (.theta loop) (.cons initial (.cons feedback .nil)))
    {i : Index l} (atZero : i loop = 0) : readRef values r i = readRef values initial i := by
  rw [at_label solves node i, interpret_theta, atZero]
  rfl

theorem theta_succ (solves : g.Solves m env values) {r initial feedback : Ref g.sort out}
    {loop : Fin l} (node : HasNode r (.theta loop) (.cons initial (.cons feedback .nil)))
    {i : Index l} {k : Nat} (atSucc : i loop = k + 1) :
    readRef values r i = readRef values feedback (i.set loop k) := by
  rw [at_label solves node i, interpret_theta, atSucc]
  rfl

theorem eval_at (solves : g.Solves m env values) {r source : Ref g.sort out}
    {count : Ref g.sort .count} {loop : Fin l}
    (node : HasNode r (.eval loop) (.cons source (.cons count .nil))) (i : Index l) :
    readRef values r i = (readRef values count i).elim none
      (fun k => monotonize (fun j => readRef values source (i.set loop j)) k.down) :=
  at_label solves node i

theorem pass_at (solves : g.Solves m env values) {r : Ref g.sort .count}
    {cond : Ref g.sort .bool} {loop : Fin l} (node : HasNode r (.pass loop) (.cons cond .nil))
    (i : Index l) : readRef values r i =
      (firstTrue (fun j => (readRef values cond (i.set loop j)).map ULift.down)).map ULift.up :=
  at_label solves node i

private theorem collect_single {ty : Ty Data}
    (read : ∀ slot : Fin ([ty] : List (Ty Data)).length,
      Option (m.Value ([ty] : List (Ty Data))[slot])) :
    collect [ty] read = (read 0).map (fun a => Tuple.cons a .nil) := by
  unfold collect
  cases read 0 <;> rfl

theorem unary_at (solves : g.Solves m env values) {r : Ref g.sort out}
    {ty : Ty Data} {arg : Ref g.sort ty} {op : P [ty] out}
    (node : HasNode r (.op op) (.cons arg .nil)) (i : Index l) :
    readRef values r i = (readRef values arg i).bind (fun a => m.run op (.cons a .nil)) := by
  rw [at_label solves node i]
  change (collect [ty] _).elim none (m.run op) = _
  rw [collect_single]
  change ((readRef values arg i).map (fun a => Tuple.cons a .nil)).elim none (m.run op) = _
  cases readRef values arg i <;> rfl

end Silmaril.SSA.PEG.Rules.Proofs
