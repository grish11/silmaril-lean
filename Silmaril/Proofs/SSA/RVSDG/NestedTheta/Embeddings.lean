module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Execution

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Proofs

universe u v w z

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs carried : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private theorem eval_base (m : Model.{u, v, w} Op) (fuel : Nat) (shape : Shape Op ins outs)
    (children : Fin shape.regionCount → Tuple m.Val shape.entry → Tuple m.Val shape.exit)
    (input : Tuple m.Val ins) :
    (Kind.base shape).eval m fuel (fun i x => some (children i x)) input =
      some (shape.eval m children input) := by
  cases shape with
  | simple => rfl
  | gamma extra => cases input; rfl

theorem term_eval_ofBase (m : Model.{u, v, w} Op) (fuel : Nat) (t : RVSDG.Term Op args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) :
    (Term.ofBase t).eval m fuel input locals = some (t.eval m input locals) := by
  induction t with
  | ret => rfl
  | bind node children rest childRuns restRuns =>
    rw [Term.ofBase, Term.eval, RVSDG.Term.eval]
    have sameChildren : (fun i x => (Term.ofBase (children i)).eval m fuel (past := []) x PUnit.unit) =
        (fun i x => some ((children i).eval m (past := []) x PUnit.unit)) :=
      funext fun i => funext fun x => childRuns i x PUnit.unit
    erw [sameChildren, eval_base]
    apply restRuns

private theorem table_ofBase (m : Model.{u, v, w} Op) (fuel : Nat) (input : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (locals : Locals m.Val past)
    (nodes : RVSDG.Nodes Op args past sigs)
    (children : (i : Fin sigs.length) → Fin (nodes i).shape.regionCount →
      Tuple m.Val (nodes i).shape.entry → Tuple m.Val (nodes i).shape.exit)
    (results : Wires args (extend past sigs) outs) :
    evalTable m fuel input past sigs locals (fun i => .ofBase (nodes i))
      (fun i j x => some (children i j x)) results =
      some (RVSDG.evalTable m input past sigs locals nodes children results) := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    let node := nodes 0
    let value := node.shape.eval m (children 0) (node.inputs.read input locals)
    let runRest (output : Tuple m.Val head) :=
      evalTable m fuel input (past ++ [head]) tail (locals.snoc output)
        (fun i => .ofBase (nodes i.succ)) (fun i j x => some (children i.succ j x)) results
    exact (congrArg (fun step => step >>= runRest)
      (eval_base m fuel node.shape (children 0) (node.inputs.read input locals))).trans
        (ih (past ++ [head]) (locals.snoc value) (fun i => nodes i.succ) (fun i => children i.succ) results)

theorem graph_eval_ofBase (m : Model.{u, v, w} Op) (fuel : Nat) (g : RVSDG.Graph Op args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) :
    (Graph.ofBase g).eval m fuel input locals = some (g.eval m input locals) := by
  induction g with
  | region nodes children results ih =>
    rw [Graph.ofBase, Graph.eval, RVSDG.Graph.eval]
    have sameChildren :
        (fun i j x => (Graph.ofBase (children i j)).eval m fuel (past := []) x PUnit.unit) =
        (fun i j x => some ((children i j).eval m (past := []) x PUnit.unit)) :=
      funext fun i => funext fun j => funext fun x => ih i j x PUnit.unit
    erw [sameChildren]
    apply table_ofBase

private theorem map_map {Ty : Type u} {F : Ty → Type v} {G : Ty → Type w} {H : Ty → Type z}
    {ts : Ports Ty} (xs : Tuple F ts) (f : ∀ t, F t → G t) (g : ∀ t, G t → H t) :
    (xs.map f).map g = xs.map (fun t x => g t (f t x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Tuple.cons (g _ (f _ x))) ih

private theorem identity_get {Ty : Type u} {F : Ty → Type w} {ts : Ports Ty} (xs : Tuple F ts) :
    (identityPorts ts).map (fun _ p => xs.get p) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [identityPorts, Tuple.map, Tuple.get, map_map]
    exact congrArg (Tuple.cons x) ih

private theorem theta_input (m : Model.{u, v, w} Op) (input : Tuple m.Val carried) :
    ((thetaVertex (Op := Op) (carried := carried) sigs).inputs.read input
      (PUnit.unit : Locals m.Val [])) = input := by
  simp only [thetaVertex, Wires.read, map_map]
  exact identity_get input

private theorem theta_output (m : Model.{u, v, w} Op) (input output : Tuple m.Val carried) :
    (thetaResults carried).read input ((output, PUnit.unit) : Locals m.Val [carried]) = output := by
  simp only [thetaResults, Wires.read, map_map]
  exact identity_get output

private theorem term_theta_eval (m : Model.{u, v, w} Op) (fuel : Nat) (t : Theta.Term Op args sigs)
    (input : Tuple m.Val args) :
    (Term.ofTheta t).run m fuel input =
      iterate (fun x => some (t.body.run m x)) (fun tag => tag.down.val == 1) fuel input := by
  let run := iterate (fun x => some (t.body.run m x)) (fun tag => tag.down.val == 1) fuel input
  have evalBody (x : Tuple m.Val args) :
      (Term.ofBase t.body).eval m fuel (past := []) x PUnit.unit = some (t.body.run m x) :=
    term_eval_ofBase m fuel t.body x PUnit.unit
  have inputEq : (thetaVertex (Op := Op) (carried := args) sigs).inputs.read input
      (PUnit.unit : Locals m.Val []) = input := theta_input m input
  change (do
    let output ← iterate (fun x => (Term.ofBase t.body).eval m fuel (past := []) x PUnit.unit)
      (fun tag => tag.down.val == 1) fuel
        ((thetaVertex (Op := Op) (carried := args) sigs).inputs.read input
          (PUnit.unit : Locals m.Val []))
    some ((thetaResults args).read input (output, PUnit.unit))) = run
  rw [inputEq, show (fun x => (Term.ofBase t.body).eval m fuel (past := []) x PUnit.unit) =
      (fun x => some (t.body.run m x)) from funext evalBody]
  change (run >>= fun output => some ((thetaResults args).read input (output, PUnit.unit))) = run
  simp only [theta_output]
  cases run <;> rfl

private theorem graph_theta_eval (m : Model.{u, v, w} Op) (fuel : Nat) (g : Theta.Graph Op args sigs)
    (input : Tuple m.Val args) :
    (Graph.ofTheta g).run m fuel input =
      iterate (fun x => some (g.body.run m x)) (fun tag => tag.down.val == 1) fuel input := by
  let run := iterate (fun x => some (g.body.run m x)) (fun tag => tag.down.val == 1) fuel input
  have evalBody (x : Tuple m.Val args) :
      (Graph.ofBase g.body).eval m fuel (past := []) x PUnit.unit = some (g.body.run m x) :=
    graph_eval_ofBase m fuel g.body x PUnit.unit
  have inputEq : (thetaVertex (Op := Op) (carried := args) sigs).inputs.read input
      (PUnit.unit : Locals m.Val []) = input := theta_input m input
  change (do
    let output ← iterate (fun x => (Graph.ofBase g.body).eval m fuel (past := []) x PUnit.unit)
      (fun tag => tag.down.val == 1) fuel
        ((thetaVertex (Op := Op) (carried := args) sigs).inputs.read input
          (PUnit.unit : Locals m.Val []))
    some ((thetaResults args).read input (output, PUnit.unit))) = run
  rw [inputEq, show (fun x => (Graph.ofBase g.body).eval m fuel (past := []) x PUnit.unit) =
      (fun x => some (g.body.run m x)) from funext evalBody]
  change (run >>= fun output => some ((thetaResults args).read input (output, PUnit.unit))) = run
  simp only [theta_output]
  cases run <;> rfl

theorem term_returns_ofTheta (m : Model.{u, v, w} Op) (t : Theta.Term Op args sigs)
    (input output : Tuple m.Val args) :
    (Term.ofTheta t).Returns m input output ↔ t.Returns m input output := by
  unfold Theta.Term.Returns
  rw [← iterate_total m (t.body.run m) input output]
  constructor
  · intro execution
    obtain ⟨bound, enough⟩ := exec_complete m (Term.ofTheta t) input PUnit.unit output execution
    exact ⟨bound, (term_theta_eval m bound t input).symm.trans (enough bound (Nat.le_refl _))⟩
  · rintro ⟨bound, evaluated⟩
    exact exec_sound m (Term.ofTheta t) bound input PUnit.unit output
      ((term_theta_eval m bound t input).trans evaluated)

theorem graph_returns_ofTheta (m : Model.{u, v, w} Op) (g : Theta.Graph Op args sigs)
    (input output : Tuple m.Val args) :
    (Graph.ofTheta g).Returns m input output ↔ g.Returns m input output := by
  unfold Graph.Returns Theta.Graph.Returns
  simp only [graph_theta_eval]
  exact iterate_total m (g.body.run m) input output

end Silmaril.SSA.RVSDG.NestedTheta.Proofs
