module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Figure19Rows

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs.Figure19

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open PEG.Figure19 (Derives FitsForest Assumptions)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params all outs before after vars inside : List (Ty Data)} {t : Ty Data}
variable {rows : Rows P params all all} {roots : Tuple (Port all) outs}
variable {depth : Fin all.length → Nat} {ctx : Assumptions all.length}
variable {parent : Option (Fin all.length)}

abbrev contextDepth (depth : Fin all.length → Nat) (parent : Option (Fin all.length)) : Nat :=
  (parent.map depth).getD 0

abbrev AtMost {n : Nat} (ctx : Assumptions n) (level : Nat) := ∀ a ∈ ctx, a.1 ≤ level

abbrev Types (rows : Rows P params all all) (roots : Tuple (Port all) outs)
    (depth : Fin all.length → Nat) (level : Nat) (ctx : Assumptions all.length)
    (embed : Embed after all) (refs : Tuple (Port after) vars) : Prop :=
  PortsSatisfy (fun r => Typed (table rows roots) depth level ctx (embed r)) refs

/-- Close a finite family of binders using only single-binder steps.
Adding an assumption removes one outstanding binder from the induction
measure. At each step, all mutually recursive values are available in
the context extended by the binder whose feedback is being proved. -/
private theorem closeBinders {A : Type} [DecidableEq A] (binders : List A)
    (goal : List A → A → Prop)
    (assume : ∀ {localCtx a}, a ∈ binders → a ∈ localCtx → goal localCtx a)
    (expand : ∀ {localCtx a}, (∀ b ∈ localCtx, b ∈ binders) → a ∈ binders →
      (∀ b ∈ binders, goal (a :: localCtx) b) → goal localCtx a) :
    ∀ a ∈ binders, goal [] a := by
  have go (remaining : List A) : ∀ (localCtx : List A),
      (∀ b ∈ localCtx, b ∈ binders) →
      (∀ b ∈ binders, b ∈ localCtx ∨ b ∈ remaining) → ∀ a ∈ binders, goal localCtx a := by
    induction remaining using (measure List.length).wf.induction with
    | h remaining ih =>
      intro localCtx inside cover a member
      by_cases found : a ∈ localCtx
      · exact assume member found
      · have pending := (cover a member).resolve_left found
        apply expand inside member
        apply ih (remaining.erase a) (by
          change (remaining.erase a).length < remaining.length
          rw [List.length_erase_of_mem pending]
          have positive := List.length_pos_of_mem pending
          omega)
        · intro b hb
          exact (List.mem_cons.mp hb).elim (fun eq => eq ▸ member) (inside b)
        · intro b hb
          by_cases same : b = a
          · exact .inl (by simp [same])
          · exact (cover b hb).imp (List.mem_cons_of_mem _) (List.mem_erase_of_ne same).mpr
  exact go binders [] (fun _ h => nomatch h) (fun _ h => .inr h)

variable {init : Tuple (Port before) vars} {body : Code P params (vars ++ before) inside}
variable {guard : Port inside .bool} {next : Tuple (Port inside) vars} {neg : P [.bool] .bool}
variable (v : View rows parent (.loop init body guard next neg))

abbrev carried (s : Port vars t) : Port all t :=
  v.inner.embed (body.lift (portLeft s))

private theorem thetaRow (s : Port vars t) :
    PEG.Figure19.nodeAt (table rows roots) (numberPort (carried v s)) =
      .ofLabel (.theta v.key)
        (.cons (numberPort (v.embed ((Code.loop init body guard next neg).lift (init.get s))))
          (.cons (numberPort (v.inner.embed (next.get s))) .nil)) := by
  have row := v.inner.node (roots := roots) (body.lift (portLeft s))
  dsimp only [View.inner] at row
  rw [rows_lift, loopHoles_left] at row
  exact row

private theorem evalRow (s : Port vars t) :
    PEG.Figure19.nodeAt (table rows roots) (numberPort (v.embed (portLeft s))) =
      .ofLabel (.eval v.key)
        (.cons (numberPort (carried v s)) (.cons (numberPort (v.embed (passRef vars))) .nil)) := by
  have row := v.node (roots := roots) (portLeft s)
  simp only [Code.rows] at row
  rw [loopRows_exit] at row
  exact row

private theorem passRow :
    PEG.Figure19.nodeAt (table rows roots) (numberPort (v.embed (passRef vars))) =
      .ofLabel (.pass v.key) (.cons (numberPort (v.embed (negRef vars))) .nil) := by
  have row := v.node (roots := roots) (passRef vars)
  simp only [Code.rows] at row
  rw [loopRows_pass] at row
  exact row

private theorem negRow :
    PEG.Figure19.nodeAt (table rows roots) (numberPort (v.embed (negRef vars))) =
      .ofLabel (.op neg) (.cons (numberPort (v.inner.embed guard)) .nil) := by
  have row := v.node (roots := roots) (negRef vars)
  simp only [Code.rows] at row
  rw [loopRows_neg] at row
  exact row

abbrev BodyTypes (v : View rows parent (.loop init body guard next neg))
    (roots : Tuple (Port all) outs) (depth : Fin all.length → Nat) : Prop :=
  ∀ localCtx : Assumptions all.length, AtMost localCtx (depth v.key) →
    (∀ t (s : Port vars t), Typed (table rows roots) depth (depth v.key) localCtx (carried v s)) →
    Typed (table rows roots) depth (depth v.key) localCtx (v.inner.embed guard) ∧
      Types rows roots depth (depth v.key) localCtx v.inner.embed next

theorem loop (fits : FitsForest (table rows roots).forest depth)
    (bounded : AtMost ctx (contextDepth depth parent))
    (entry : Types rows roots depth (contextDepth depth parent) ctx
      (fun r => v.embed ((Code.loop init body guard next neg).lift r)) init)
    (insideTyped : BodyTypes v roots depth) :
    ∀ t (s : Port vars t), Typed (table rows roots) depth (contextDepth depth parent) ctx
      (v.embed (portLeft s)) := by
  have succ : depth v.key = contextDepth depth parent + 1 := v.keyDepth fits
  have deeper : contextDepth depth parent < depth v.key := by rw [succ]; exact Nat.lt_succ_self _
  let binder {t} (s : Port vars t) : Nat × Fin all.length :=
    (depth v.key, (numberPort (carried v s)).id)
  let binders := (List.finRange vars.length).map (fun slot => binder (portAt vars slot))
  have member (t : Ty Data) (s : Port vars t) : binder s ∈ binders :=
    WhileProofs.portForall vars (fun _ p => binder p ∈ binders)
      (fun j => List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) t s
  let goal (localCtx : Assumptions all.length) (a : Nat × Fin all.length) : Prop :=
    Derives (table rows roots) depth .inward (depth v.key) (localCtx ++ ctx) a.2
  have closed : ∀ a ∈ binders, goal [] a := by
    apply closeBinders binders goal
    · intro localCtx a haveBinder active
      obtain ⟨slot, _, rfl⟩ := List.mem_map.mp haveBinder
      exact assumeAt (thetaRow (roots := roots) v (portAt vars slot)) (List.mem_append_left _ active)
    · intro localCtx a localBound haveBinder nextBinder
      obtain ⟨slot, _, rfl⟩ := List.mem_map.mp haveBinder
      let s := portAt vars slot
      have extBound : AtMost ((binder s :: localCtx) ++ ctx) (depth v.key) := by
        intro b h
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_cons.mp h with rfl | old
          · exact Nat.le_refl _
          · obtain ⟨j, _, rfl⟩ := List.mem_map.mp (localBound b old)
            exact Nat.le_refl _
        · exact Nat.le_trans (bounded b h) (Nat.le_of_lt deeper)
      have nextRows := (insideTyped _ extBound (fun t r => nextBinder (binder r) (member t r))).2
      exact thetaAt (thetaRow (roots := roots) v s) succ
        (.reduce (Nat.le_refl _) (fun _ h => List.mem_append_right _ h) (entry _ s)) (nextRows _ s)
  have carriedTyped (t : Ty Data) (s : Port vars t) :
      Typed (table rows roots) depth (depth v.key) ctx (carried v s) :=
    closed (binder s) (member t s)
  have guardTyped := (insideTyped ctx (fun a h => Nat.le_trans (bounded a h) (Nat.le_of_lt deeper)) carriedTyped).1
  have predicate : Typed (table rows roots) depth (depth v.key) ctx (v.embed (negRef vars)) := by
    apply opAt (negRow (roots := roots) v)
    intro slot
    exact Fin.cases guardTyped (fun i => i.elim0) slot
  intro t s
  exact evalAt (evalRow (roots := roots) v s) (passRow (roots := roots) v) succ
    (fun a h => Nat.lt_of_le_of_lt (bounded a h) deeper) (carriedTyped t s) predicate

end Silmaril.SSA.PEG.Simple.Structured.Proofs.Figure19
