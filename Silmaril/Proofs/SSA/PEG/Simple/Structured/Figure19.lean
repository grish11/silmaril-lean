module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Figure19Loop

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs.Figure19

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open PEG.Figure19 (Assumptions FitsForest CFGContext inferDepth)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params all results before after vars outs : List (Ty Data)} {t : Ty Data}
variable {rows : Rows P params all all} {roots : Tuple (Port all) results}
variable {parent : Option (Fin all.length)} {depth : Fin all.length → Nat}
variable {localCtx : Assumptions all.length}

private theorem lifted (code : Code P params before after) (embed : Embed after all)
    {refs : Tuple (Port before) vars}
    (entry : Types rows roots depth (contextDepth depth parent) localCtx (fun r => embed (code.lift r)) refs) :
    Types rows roots depth (contextDepth depth parent) localCtx embed (code.liftRefs refs) :=
  satisfyMap (fun r => code.lift r) entry (fun _ _ h => h)

private theorem straightBuild (b : Simple.Build P params before outs)
    (v : View rows parent (.straight b.code))
    (ok : StraightBuildChecks (fun r =>
      Typed (table rows roots) depth (contextDepth depth parent) localCtx (v.embed (b.code.lift r))) b) :
    Types rows roots depth (contextDepth depth parent) localCtx v.embed b.refs :=
  fun t s => straight b.code v.holes v.embed v.eqs _ ok.1 (fun _ _ h => h) t _ (ok.2 t s)

private theorem exprTyped (e : Expr P vars t) (refs : Tuple (Port before) vars)
    (v : View rows parent (expr (params := params) e refs).code)
    (entry : Types rows roots depth (contextDepth depth parent) localCtx
      (fun r => v.embed ((expr (params := params) e refs).code.lift r)) refs) :
    Types rows roots depth (contextDepth depth parent) localCtx v.embed (expr e refs).refs :=
  straightBuild (e.lower refs) v (exprChecks params e refs entry)

/-- The input and output store references have derivations at the
containing depth. The invariant ranges over every bounded outer
assumption context so a loop body can be typed after introducing a θ. -/
private def LowerTyped (rows : Rows P params all all) (roots : Tuple (Port all) results)
    (depth : Fin all.length → Nat) (neg : P [.bool] .bool) (stmt : Stmt P true vars outs) : Prop :=
  ∀ {before : List (Ty Data)} (refs : Tuple (Port before) vars)
    {parent : Option (Fin all.length)} (v : View rows parent (lower (params := params) neg stmt refs).code)
    {localCtx : Assumptions all.length}, AtMost localCtx (contextDepth depth parent) →
    Types rows roots depth (contextDepth depth parent) localCtx
      (fun r => v.embed ((lower (params := params) neg stmt refs).code.lift r)) refs →
    Types rows roots depth (contextDepth depth parent) localCtx v.embed (lower neg stmt refs).refs

private theorem lowerTyped (fits : FitsForest (table rows roots).forest depth)
    (neg : P [.bool] .bool) (stmt : Stmt P true vars outs) :
    LowerTyped rows roots depth neg stmt := by
  induction stmt with
  | assign e =>
    intro before refs parent v localCtx _ entry
    have value := exprTyped e refs v entry
    exact satisfyCons (value _ .head) (lifted (expr e refs).code v.embed entry)
  | project slots =>
    intro before refs parent v localCtx _ entry t s
    change Typed (table rows roots) depth (contextDepth depth parent) localCtx
      (v.embed ((select refs slots).get s))
    rw [Simple.Proofs.get_select]
    exact entry _ (slots.get s)
  | seq a b ihA ihB =>
    intro before refs parent v localCtx bound entry
    let left := lower (params := params) neg a refs
    let right := lower (params := params) neg b left.refs
    change View rows parent (.seq left.code right.code) at v
    exact ihB left.refs v.right bound (ihA refs v.left bound entry)
  | branch test yes no ihYes ihNo =>
    intro before refs parent v localCtx bound entry
    let c := expr (params := params) test refs
    let cRefs := c.code.liftRefs refs
    let y := lower (params := params) neg yes cRefs
    let n := lower (params := params) neg no (y.code.liftRefs cRefs)
    let flag := n.code.lift (y.code.lift (c.refs.get .head))
    let join := phiNodes (P := P) (params := params) flag (n.code.liftRefs y.refs) n.refs
    change View rows parent (.seq c.code (.seq y.code (.seq n.code (.straight join.code)))) at v
    have guardTyped := exprTyped test refs v.left entry
    have yEntry := lifted c.code v.left.embed entry
    have yTyped := ihYes cRefs v.right.left bound yEntry
    have nEntry := lifted y.code v.right.left.embed yEntry
    have nTyped := ihNo (y.code.liftRefs cRefs) v.right.right.left bound nEntry
    have yesArm := lifted n.code v.right.right.left.embed yTyped
    exact straightBuild join v.right.right.right
      (phiChecks flag (n.code.liftRefs y.refs) n.refs (guardTyped _ .head) yesArm nTyped)
  | @«while» carried _ test body ih =>
    intro before refs parent v localCtx bound entry
    let slots := (ports carried).map (fun _ r => portLeft (right := before) r)
    let c := expr (params := params) test slots
    let b := lower (params := params) neg body (c.code.liftRefs slots)
    change View rows parent (.loop refs (.seq c.code b.code) (b.code.lift (c.refs.get .head)) b.refs neg) at v
    have innerTyped : BodyTypes v roots depth := by
      intro assumptions innerBound seed
      have cEntry : Types rows roots depth (depth v.key) assumptions
          (fun r => v.inner.left.embed (c.code.lift r)) slots := by
        intro t s
        change Typed (table rows roots) depth (depth v.key) assumptions
          (v.inner.left.embed (c.code.lift (slots.get s)))
        rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
        exact seed t s
      exact ⟨exprTyped test slots v.inner.left cEntry _ .head,
        ih (c.code.liftRefs slots) v.inner.right innerBound (lifted c.code v.inner.left.embed cEntry)⟩
    intro t slot
    change Typed (table rows roots) depth (contextDepth depth parent) localCtx
      (v.embed ((ports carried).map (fun _ r => portLeft r) |>.get slot))
    rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
    exact loop v fits bound entry innerTyped t slot

private theorem inferDepth_stable {n : Nat} (forest : LoopForest n)
    (earlier : ∀ i j, forest.parent i = some j → j.val < i.val)
    (i : Fin n) (a b : Nat) (left : i.val < a) (right : i.val < b) :
    inferDepth forest a i = inferDepth forest b i := by
  cases a with
  | zero => omega
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [inferDepth]
      cases parent : forest.parent i with
      | none => rfl
      | some j =>
        have less := earlier i j parent
        rw [Option.map_some, Option.map_some, Option.getD_some, Option.getD_some]
        rw [inferDepth_stable forest earlier j a b (by omega) (by omega)]
termination_by i.val
decreasing_by exact less

private theorem depthFits {n : Nat} (forest : LoopForest n)
    (earlier : ∀ i j, forest.parent i = some j → j.val < i.val) :
    FitsForest forest (inferDepth forest n) := by
  cases n with
  | zero => intro i; exact i.elim0
  | succ n =>
    intro i
    rw [inferDepth]
    cases parent : forest.parent i with
    | none => rfl
    | some j =>
      have less := earlier i j parent
      have bound := i.isLt
      simp only [Option.map_some, Option.getD_some]
      rw [inferDepth_stable forest earlier j n (n + 1) (by omega) (by omega)]

theorem programTyped (p : Program P true params t) (neg : P [.bool] .bool) :
    let g := translate p neg
    FitsForest g.forest (inferDepth g.forest (program p neg).nodes.length) ∧
      CFGContext g (inferDepth g.forest (program p neg).nodes.length) .inward := by
  let compiled := program p neg
  let init := Build.straight (paramNodes (P := P) (nodes := []) (ports params))
  let body := lower (params := params) neg p.body init.refs
  let rows : Rows P params compiled.nodes compiled.nodes :=
    compiled.code.rows (fun r => nomatch r) (fun r => r) none
  let g := table rows compiled.refs
  let depth := inferDepth g.forest compiled.nodes.length
  have fits : FitsForest g.forest depth :=
    depthFits g.forest (earlierParent compiled.code compiled.refs)
  refine ⟨fits, ?_⟩
  let view : View rows none (.seq init.code body.code) :=
    { holes := fun r => nomatch r
      embed := fun r => r
      eqs := fun _ _ => rfl }
  have inputs : Types rows compiled.refs depth 0 [] view.left.embed init.refs :=
    straightBuild (paramNodes (P := P) (nodes := []) (ports params)) view.left (paramChecks _ _)
  have result := lowerTyped (roots := compiled.refs) fits neg p.body init.refs view.right
    (localCtx := []) (fun _ h => nomatch h) inputs t p.retvar
  intro slot
  have zero : slot = 0 := Fin.ext (by
    have bound := slot.isLt
    change slot.val < 1 at bound
    change slot.val = 0
    omega)
  subst slot
  exact result

end Silmaril.SSA.PEG.Simple.Structured.Proofs.Figure19
