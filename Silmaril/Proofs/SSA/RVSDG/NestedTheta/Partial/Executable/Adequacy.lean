module

public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Proofs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {m : Model.{u,v,w} Op}
variable {args ins outs : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}

private def Adequate {X : Type*} (run : Nat → Option X) (returns : X → Prop) : Prop :=
  (∀ fuel output, run fuel = some output → returns output) ∧
  (∀ output, returns output → ∃ bound, ∀ fuel, bound ≤ fuel → run fuel = some output)

private theorem bind_adequate {X Y : Type*} {step : Nat → Option X}
    {rest : Nat → X → Option Y} {first : X → Prop} {next : X → Y → Prop}
    (hstep : Adequate step first) (hrest : ∀ x, Adequate (fun f => rest f x) (next x)) :
    Adequate (fun f => (step f).bind (rest f)) (fun y => ∃ x, first x ∧ next x y) := by
  constructor
  · intro fuel output h
    obtain ⟨x, run, tail⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨x, hstep.1 fuel x run, (hrest x).1 fuel output tail⟩
  · rintro output ⟨x, firstRun, restRun⟩
    obtain ⟨a, ha⟩ := hstep.2 x firstRun
    obtain ⟨b, hb⟩ := (hrest x).2 output restRun
    refine ⟨max a b, fun fuel enough => ?_⟩
    exact Option.bind_eq_some_iff.mpr
      ⟨x, ha fuel (Nat.le_trans (Nat.le_max_left _ _) enough),
        hb fuel (Nat.le_trans (Nat.le_max_right _ _) enough)⟩

private theorem tag_eq (tag : ULift.{w} (Fin 2)) (values : Tuple m.Val ins) :
    (Tuple.cons tag values : Tuple m.Val (Theta.BodyResults ins)) = tagged m (tag.down.val == 1) values := by
  obtain ⟨tag⟩ := tag
  exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)) tag

private theorem iterate_sound
    {body : Tuple m.Val ins → Option (Tuple m.Val (Theta.BodyResults ins))}
    {derives : Tuple m.Val ins → Tuple m.Val (Theta.BodyResults ins) → Prop}
    (sound : ∀ x y, body x = some y → derives x y)
    (fuel : Nat) {input output : Tuple m.Val ins}
    (h : iterate body (fun tag => tag.down.val == 1) fuel input = some output) :
    Theta.Iterate (fun x again y => derives x (tagged m again y)) input output := by
  induction fuel generalizing input with
  | zero => cases h
  | succ fuel ih =>
    cases step : body input with
    | none => simp [iterate, step] at h
    | some result =>
      cases result with
      | cons tag next =>
        have derived := sound _ _ step
        rw [tag_eq tag next] at derived
        rw [iterate, step] at h
        cases branch : (tag.down.val == 1) with
        | false =>
          simp only [branch, Bool.false_eq_true, ite_false, Option.some.injEq] at h
          rw [branch] at derived
          exact h ▸ Theta.Iterate.stop derived
        | true =>
          simp only [branch, ite_true] at h
          rw [branch] at derived
          exact .again derived (ih h)

private theorem iterate_step
    (body : Tuple m.Val ins → Option (Tuple m.Val (Theta.BodyResults ins)))
    (remaining : Nat) {input next : Tuple m.Val ins} {again : Bool}
    (step : body input = some (tagged m again next)) :
    iterate body (fun tag => tag.down.val == 1) (remaining + 1) input =
      (if again then iterate body (fun tag => tag.down.val == 1) remaining next else some next) := by
  cases observed : body input with
  | none =>
    have impossible := observed.symm.trans step
    cases impossible
  | some payload =>
    have equal : payload = tagged m again next := Option.some.inj (observed.symm.trans step)
    rw [iterate, observed, equal]
    cases again <;> rfl

private theorem iterate_complete
    {body : Nat → Tuple m.Val ins → Option (Tuple m.Val (Theta.BodyResults ins))}
    {derives : Tuple m.Val ins → Tuple m.Val (Theta.BodyResults ins) → Prop}
    (complete : ∀ x, Adequate (fun fuel => body fuel x) (derives x))
    {input output : Tuple m.Val ins}
    (h : Theta.Iterate (fun x again y => derives x (tagged m again y)) input output) :
    ∃ bound, ∀ fuel remaining, bound ≤ fuel → bound ≤ remaining →
      iterate (body fuel) (fun tag => tag.down.val == 1) remaining input = some output := by
  induction h with
  | @stop input output step =>
    obtain ⟨b, run⟩ := (complete input).2 _ step
    refine ⟨max 1 b, fun fuel remaining enough count => ?_⟩
    cases remaining with
    | zero => omega
    | succ remaining =>
      exact iterate_step (body fuel) remaining (again := false)
        (run fuel (Nat.le_trans (Nat.le_max_right _ _) enough))
  | @again input next output step _ ih =>
    obtain ⟨b, run⟩ := (complete input).2 _ step
    obtain ⟨r, tail⟩ := ih
    refine ⟨max b (r + 1), fun fuel remaining enough count => ?_⟩
    cases remaining with
    | zero => omega
    | succ remaining =>
      exact (iterate_step (body fuel) remaining (again := true)
        (run fuel (Nat.le_trans (Nat.le_max_left _ _) enough))).trans
          (tail fuel remaining (by omega) (by omega))

private theorem kind_adequate (actions : Actions m) (kind : Kind Op ins outs)
    (eval : Nat → Fin kind.arity → Tuple m.Val kind.entry → Option (Tuple m.Val kind.exit))
    (exec : Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop)
    (child : ∀ j x, Adequate (fun fuel => eval fuel j x) (exec j x)) (input : Tuple m.Val ins) :
    Adequate (fun fuel => kindEval actions fuel kind (eval fuel) input) (kindExec m kind exec input) := by
  cases kind with
  | base shape =>
    cases shape with
    | simple op =>
      have step (output : Tuple m.Val outs) :
          actions.primitive op input = some output ↔ output ∈ m.primitive op input := by
        rw [← actions.agrees op input, Part.mem_ofOption, Option.mem_def]
      exact ⟨fun _ output => (step output).mp, fun output h => ⟨0, fun _ _ => (step output).mpr h⟩⟩
    | gamma =>
      cases input with | cons tag payload => exact child tag.down payload
  | theta =>
    exact ⟨fun fuel output h => iterate_sound (fun x y => (child (0 : Fin 1) x).1 fuel y) fuel h,
      fun _ h => by
        obtain ⟨bound, enough⟩ := iterate_complete (child (0 : Fin 1)) h
        exact ⟨bound, fun fuel le => enough fuel fuel le le⟩⟩

private theorem table_adequate (actions : Actions m) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (locals : Locals m.Val past) (nodes : Nodes Op args past sigs)
    (children : (i : Fin sigs.length) → Children (Term Op) (nodes i))
    (eval : (fuel : Nat) → TableEvaluators (F := m.Val) nodes)
    (child : ∀ i j input, Adequate (fun fuel => eval fuel i j input)
      (Partial.exec m (children i j) input PUnit.unit))
    (results : Wires args (extend past sigs) outs) :
    Adequate (fun fuel => evalTableWith (kindEval actions fuel) entry past sigs locals nodes (eval fuel) results)
      (Partial.exec m (Term.fromTable past sigs nodes children results) entry locals) := by
  induction sigs generalizing past with
  | nil => exact ⟨fun _ _ h => Option.some.inj h, fun _ h => ⟨0, fun _ _ => congrArg some h⟩⟩
  | cons head tail ih =>
    exact bind_adequate
      (kind_adequate actions (nodes 0).kind (fun fuel => eval fuel 0) _ (child 0)
        ((nodes 0).inputs.read entry locals))
      (fun result => ih (past ++ [head]) (locals.snoc result) (fun i => nodes i.succ)
        (fun i => children i.succ) (fun fuel i => eval fuel i.succ) (fun i => child i.succ) results)

private theorem graph_adequate (actions : Actions m) (g : Graph Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    Adequate (fun fuel => g.evalWith (kindEval actions fuel) entry locals) (Partial.exec m g.toTerm entry locals) := by
  induction g with
  | region nodes children results ih =>
    exact table_adequate actions entry _ _ locals nodes (fun i j => (children i j).toTerm)
      (fun fuel i j input => (children i j).evalWith (kindEval actions fuel) input PUnit.unit)
      (fun i j input => ih i j input PUnit.unit) results

theorem returns_iff (actions : Actions m) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    (∃ fuel, run actions g fuel input = some output) ↔ Partial.returns m g input output := by
  have adequate := graph_adequate actions g input PUnit.unit
  constructor
  · rintro ⟨fuel, h⟩
    exact adequate.1 fuel output h
  · intro h
    obtain ⟨bound, enough⟩ := adequate.2 output h
    exact ⟨bound, enough bound (Nat.le_refl bound)⟩

end Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Proofs
