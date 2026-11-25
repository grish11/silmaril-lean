module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Correspondence

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs carried : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}

private theorem decode (m : Model.{u, v, w} Op) (tag : ULift.{w} (Fin 2))
    (values : Tuple m.Val carried) :
    (Tuple.cons tag values : Tuple m.Val (Theta.BodyResults carried)) =
      Theta.bodyResult m (tag.down.val == 1) values := by
  obtain ⟨tag⟩ := tag
  exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)) tag

private abbrev Body (m : Model.{u, v, w} Op) (ts : Ports (PortType V S)) :=
  Tuple m.Val ts → Tuple m.Val (Theta.BodyResults ts) → Prop

private theorem iterate_sound (m : Model.{u, v, w} Op) (exec : Body m carried)
    (body : Tuple m.Val carried → Option (Tuple m.Val (Theta.BodyResults carried)))
    (sound : ∀ input output, body input = some output → exec input output)
    (fuel : Nat) (input output : Tuple m.Val carried)
    (h : iterate body (fun tag => tag.down.val == 1) fuel input = some output) :
    Theta.Iterate (fun x again y => exec x (Theta.bodyResult m again y)) input output := by
  induction fuel generalizing input with
  | zero => cases h
  | succ fuel ih =>
    cases run : body input with
    | none => simp [iterate, run] at h
    | some result =>
      cases result with
      | cons tag next =>
        have step := sound _ _ run
        rw [decode m tag next] at step
        rw [iterate, run] at h
        change (if tag.down.val == 1 then iterate body (fun x => x.down.val == 1) fuel next
          else some next) = some output at h
        cases branch : (tag.down.val == 1) with
        | false =>
          simp [branch] at h
          rw [branch] at step
          exact h ▸ Theta.Iterate.stop step
        | true =>
          simp [branch] at h
          rw [branch] at step
          exact .again step (ih next h)

private theorem iterate_complete (m : Model.{u, v, w} Op) (exec : Body m carried)
    (body : Nat → Tuple m.Val carried → Option (Tuple m.Val (Theta.BodyResults carried)))
    (complete : ∀ input output, exec input output →
      ∃ limit, ∀ fuel, limit ≤ fuel → body fuel input = some output)
    (input output : Tuple m.Val carried)
    (h : Theta.Iterate (fun x again y => exec x (Theta.bodyResult m again y)) input output) :
    ∃ limit, ∀ fuel remaining, limit ≤ fuel → limit ≤ remaining →
      iterate (body fuel) (fun tag => tag.down.val == 1) remaining input = some output := by
  induction h with
  | @stop start finish step =>
    obtain ⟨bound, run⟩ := complete _ _ step
    refine ⟨max 1 bound, fun fuel remaining fuelOk countOk => ?_⟩
    cases remaining with
    | zero => omega
    | succ remaining =>
      rw [iterate, run _ (Nat.le_trans (Nat.le_max_right _ _) fuelOk)]
      rfl
  | @again start next finish step remaining ih =>
    obtain ⟨bound, run⟩ := complete _ _ step
    obtain ⟨restBound, restRun⟩ := ih
    refine ⟨max bound (restBound + 1), fun fuel remaining fuelOk countOk => ?_⟩
    cases remaining with
    | zero => omega
    | succ remaining =>
      have fuelRest := Nat.le_trans (Nat.le_max_right bound (restBound + 1)) fuelOk
      have countRest := Nat.le_trans (Nat.le_max_right bound (restBound + 1)) countOk
      rw [iterate, run _ (Nat.le_trans (Nat.le_max_left _ _) fuelOk)]
      exact restRun fuel remaining (by omega) (by omega)

theorem iterate_total (m : Model.{u, v, w} Op)
    (body : Tuple m.Val carried → Tuple m.Val (Theta.BodyResults carried))
    (input output : Tuple m.Val carried) :
    (∃ fuel, iterate (fun x => some (body x)) (fun tag => tag.down.val == 1) fuel input = some output) ↔
      Theta.Iterate (fun x again y => body x = Theta.bodyResult m again y) input output := by
  constructor
  · rintro ⟨fuel, run⟩
    exact iterate_sound m (fun x y => body x = y) _ (fun _ _ => Option.some.inj) fuel _ _ run
  · intro execution
    obtain ⟨limit, succeeds⟩ := iterate_complete m (fun x y => body x = y) (fun _ x => some (body x))
      (fun _ _ h => ⟨0, fun _ _ => congrArg some h⟩) _ _ execution
    exact ⟨limit, succeeds limit limit (Nat.le_refl _) (Nat.le_refl _)⟩

private theorem kind_sound (m : Model.{u, v, w} Op) (kind : Kind Op ins outs) (fuel : Nat)
    (eval : Fin kind.arity → Tuple m.Val kind.entry → Option (Tuple m.Val kind.exit))
    (exec : Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop)
    (sound : ∀ i x y, eval i x = some y → exec i x y)
    (input : Tuple m.Val ins) (output : Tuple m.Val outs) (h : kind.eval m fuel eval input = some output) :
    kind.Exec m exec input output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode => exact Option.some.inj h
    | gamma n => cases input with | cons tag entry => exact sound tag.down entry output h
  | theta => exact iterate_sound m (exec (0 : Fin 1)) _ (sound (0 : Fin 1)) fuel input output h

private theorem kind_complete (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    (eval : Nat → Fin kind.arity → Tuple m.Val kind.entry → Option (Tuple m.Val kind.exit))
    (exec : Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop)
    (complete : ∀ i x y, exec i x y → ∃ limit, ∀ fuel, limit ≤ fuel → eval fuel i x = some y)
    (input : Tuple m.Val ins) (output : Tuple m.Val outs) (h : kind.Exec m exec input output) :
    ∃ limit, ∀ fuel, limit ≤ fuel → kind.eval m fuel (eval fuel) input = some output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode => exact ⟨0, fun _ _ => congrArg some h⟩
    | gamma n => cases input with | cons tag entry => exact complete tag.down entry output h
  | theta =>
    obtain ⟨limit, run⟩ := iterate_complete m (exec (0 : Fin 1)) (fun fuel => eval fuel (0 : Fin 1))
      (complete (0 : Fin 1)) input output h
    exact ⟨limit, fun fuel enough => run fuel fuel enough enough⟩

theorem exec_sound (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs) (fuel : Nat)
    (input : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs)
    (h : t.eval m fuel input locals = some output) : t.Exec m input locals output := by
  induction t with
  | ret wires => exact Option.some.inj h
  | bind node children rest childSound restSound =>
    simp only [Term.eval] at h
    cases first : node.kind.eval m fuel
        (fun i x => (children i).eval m fuel (past := []) x PUnit.unit)
        (node.inputs.read input locals) with
    | none => rw [first] at h; cases h
    | some found =>
      rw [first] at h
      exact ⟨found, kind_sound m node.kind fuel _ _ (fun i x y => childSound i x PUnit.unit y)
        _ _ first, restSound input (locals.snoc found) output h⟩

theorem exec_complete (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs)
    (h : t.Exec m input locals output) :
    ∃ limit, ∀ fuel, limit ≤ fuel → t.eval m fuel input locals = some output := by
  induction t with
  | ret wires => exact ⟨0, fun _ _ => congrArg some h⟩
  | bind node children rest childComplete restComplete =>
    obtain ⟨value, nodeRun, restRun⟩ := h
    obtain ⟨nodeBound, nodeEval⟩ := kind_complete m node.kind
      (fun fuel i x => (children i).eval m fuel (past := []) x PUnit.unit)
      (fun i x y => (children i).Exec m (past := []) x PUnit.unit y)
      (fun i x y => childComplete i x PUnit.unit y) _ value nodeRun
    obtain ⟨restBound, restEval⟩ := restComplete input (locals.snoc value) output restRun
    refine ⟨max nodeBound restBound, fun fuel enough => ?_⟩
    rw [Term.eval, nodeEval fuel (Nat.le_trans (Nat.le_max_left _ _) enough)]
    exact restEval fuel (Nat.le_trans (Nat.le_max_right _ _) enough)

theorem returns_iff (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    g.Returns m input output ↔ g.toTerm.Returns m input output := by
  constructor
  · rintro ⟨fuel, run⟩
    exact exec_sound m g.toTerm fuel input PUnit.unit output ((eval_toTerm g m fuel input PUnit.unit).trans run)
  · intro execution
    obtain ⟨limit, enough⟩ := exec_complete m g.toTerm input PUnit.unit output execution
    exact ⟨limit, (eval_toTerm g m limit input PUnit.unit).symm.trans (enough limit (Nat.le_refl _))⟩

theorem returns_eventually (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) (h : g.Returns m input output) :
    ∃ limit, ∀ fuel, limit ≤ fuel → g.run m fuel input = some output := by
  obtain ⟨limit, run⟩ := exec_complete m g.toTerm input PUnit.unit output ((returns_iff g m input output).1 h)
  exact ⟨limit, fun fuel enough => (eval_toTerm g m fuel input PUnit.unit).symm.trans (run fuel enough)⟩

end Silmaril.SSA.RVSDG.NestedTheta.Proofs
