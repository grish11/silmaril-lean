module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Loop

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before after vars outs all : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params} {read : Reads m all}
variable {active : List (Fin all.length)} {fixed : Index all.length}

private theorem liftRefs (code : Code P params before after) (embed : Embed after all)
    {ctx : Tuple (Port before) vars} {store : Tuple m.Value vars}
    (h : RealizesOn read (fun r => embed (code.lift r)) ctx store active fixed) :
    RealizesOn read embed (code.liftRefs ctx) store active fixed := by
  intro i agree t slot
  unfold Code.liftRefs
  rw [Simple.Proofs.get_map]
  exact h i agree t slot

private theorem exprRead (e : Expr P vars t) (ctx : Tuple (Port before) vars)
    (v : View m env read active (expr e ctx).code) {i : Index all.length}
    (store : Tuple m.Value vars)
    (entry : RealizesAt read (fun r => v.embed ((expr e ctx).code.lift r)) ctx store i)
    {value : m.Value t} (run : e.eval m store = some value) :
    read (v.embed ((expr e ctx).refs.get .head)) i = some value := by
  let b := e.lower (params := params) ctx
  change View m env read active (.straight b.code) at v
  exact (v.straightRead i (b.refs.get .head)).trans
    (Simple.Proofs.expr_correct m env e ctx (v.seed i) store (v.seedRealizes entry) run)

private theorem phiRead {cond : Port before .bool}
    {yes no : Tuple (Port before) outs}
    (v : View m env read active (.straight (phiNodes cond yes no).code))
    {i : Index all.length} {b : Bool} {store : Tuple m.Value outs}
    (test : read (v.embed ((phiNodes (P := P) (params := params) cond yes no).code.lift cond)) i = some ⟨b⟩)
    (arm : RealizesAt read (fun r => v.embed ((phiNodes cond yes no).code.lift r))
      (if b then yes else no) store i) :
    RealizesAt read v.embed (phiNodes cond yes no).refs store i := by
  let joined := phiNodes (P := P) (params := params) cond yes no
  have testSeed : (v.seed i).get cond = some ⟨b⟩ := by
    unfold View.seed
    rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
    exact test
  have h := Simple.Proofs.phi_correct m env cond yes no (v.seed i) b testSeed store (v.seedRealizes arm)
  intro t slot
  exact (v.straightRead i (joined.refs.get slot)).trans (h t slot)

private def Correct (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params) (read : Reads m all)
    (neg : P [.bool] .bool) (s : Stmt P true vars outs) : Prop :=
  ∀ {before : List (Ty Data)} (ctx : Tuple (Port before) vars)
    {active : List (Fin all.length)} (v : View m env read active (lower neg s ctx).code)
    (fixed : Index all.length) {store : Tuple m.Value vars} {final : Tuple m.Value outs},
    RealizesOn read (fun r => v.embed ((lower neg s ctx).code.lift r)) ctx store active fixed →
    Exec m s store (some final) →
    RealizesOn read v.embed (lower neg s ctx).refs final active fixed

private theorem branchCorrect (neg : P [.bool] .bool) (test : Expr P vars .bool)
    (yes no : Stmt P true vars outs)
    (yesCorrect : Correct m env read neg yes) (noCorrect : Correct m env read neg no)
    (ctx : Tuple (Port before) vars) (v : View m env read active (lower neg (.branch test yes no) ctx).code)
    (fixed : Index all.length) {store : Tuple m.Value vars} {final : Tuple m.Value outs}
    (entry : RealizesOn read (fun r => v.embed ((lower neg (.branch test yes no) ctx).code.lift r))
      ctx store active fixed)
    (b : Bool) (condition : test.eval m store = some ⟨b⟩)
    (run : Exec m (if b then yes else no) store (some final)) :
    RealizesOn read v.embed (lower neg (.branch test yes no) ctx).refs final active fixed := by
  let c := expr (params := params) test ctx
  let cRefs := c.code.liftRefs ctx
  let y := lower (params := params) neg yes cRefs
  let n := lower (params := params) neg no (y.code.liftRefs cRefs)
  let flag := n.code.lift (y.code.lift (c.refs.get .head))
  let join := phiNodes (P := P) (params := params) flag (n.code.liftRefs y.refs) n.refs
  change View m env read active (.seq c.code (.seq y.code (.seq n.code (.straight join.code)))) at v
  have afterGuard := liftRefs c.code (fun r => v.left.embed r) entry
  have afterYes := liftRefs y.code (fun r => v.right.left.embed r) afterGuard
  have selected :
      RealizesOn read (fun r => v.right.right.right.embed (join.code.lift r))
        (if b then n.code.liftRefs y.refs else n.refs) final active fixed := by
    cases b with
    | false =>
      exact noCorrect (y.code.liftRefs cRefs) v.right.right.left fixed afterYes run
    | true =>
      have yesValue := yesCorrect cRefs v.right.left fixed afterGuard run
      exact liftRefs n.code (fun r => v.right.right.left.embed r) yesValue
  intro i agree
  have flagValue := exprRead test ctx v.left store (entry i agree) condition
  exact phiRead v.right.right.right flagValue (selected i agree)

private theorem lowerCorrect (neg : P [.bool] .bool)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (s : Stmt P true vars outs) : Correct m env read neg s := by
  induction s with
  | assign e =>
    intro before ctx active v fixed store final entry run
    cases run with
    | assign op =>
      let a := expr (params := params) e ctx
      change View m env read active a.code at v
      have previous := liftRefs a.code (fun r => v.embed r) entry
      intro i agree t slot
      cases slot with
      | head => exact exprRead e ctx v store (entry i agree) op
      | tail slot => exact previous i agree _ slot
  | project selectSlots =>
    intro before ctx active v fixed store final entry run
    cases run
    intro i agree t slot
    change read (v.embed ((select ctx selectSlots).get slot)) i = some ((select store selectSlots).get slot)
    rw [Simple.Proofs.get_select, Simple.Proofs.get_select]
    exact entry i agree _ (selectSlots.get slot)
  | seq first second ihFirst ihSecond =>
    intro before ctx active v fixed store final entry run
    cases run with
    | seq firstRun secondRun =>
      let a := lower (params := params) neg first ctx
      let b := lower (params := params) neg second a.refs
      change View m env read active (.seq a.code b.code) at v
      exact ihSecond a.refs v.right fixed (ihFirst ctx v.left fixed entry firstRun) secondRun
  | branch test yes no ihYes ihNo =>
    intro before ctx active v fixed store final entry run
    cases run with
    | branchTrue h selected => exact branchCorrect neg test yes no ihYes ihNo ctx v fixed entry true h selected
    | branchFalse h selected => exact branchCorrect neg test yes no ihYes ihNo ctx v fixed entry false h selected
  | @«while» carried enabled test stmt ih =>
    intro before ctx active v fixed store final entry run
    let slots := (ports carried).map (fun _ r => portLeft (right := before) r)
    let c := expr (params := params) test slots
    let b := lower (params := params) neg stmt (c.code.liftRefs slots)
    change View m env read active (.loop ctx (.seq c.code b.code) (b.code.lift (c.refs.get .head)) b.refs neg) at v
    apply loopCorrect v negSem fixed (test := test) (stmt := stmt) ?_ ?_ entry run
    · intro k current flag carries testEval j agree
      exact exprRead test slots v.inner.left current
        (carries _ (sampleAgrees v agree k)) testEval
    · intro k current updated carries step
      have nextEntry := liftRefs c.code (fun r => v.inner.left.embed r) carries
      exact ih (c.code.liftRefs slots) v.inner.right (fixed.set v.key k) nextEntry step

theorem programReturns (p : Program P true params t) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {value : m.Value t} (run : p.Returns m env value)
    {val : (translate p neg).Valuation m} (solves : (translate p neg).Solves m env val)
    (i : Index (program p neg).nodes.length) :
    (translate p neg).observe m val i = .cons (some value) .nil := by
  obtain ⟨final, exec, returned⟩ := run
  let compiled := program p neg
  let init := Build.straight (paramNodes (P := P) (params := params) (nodes := []) (ports params))
  let body := lower (params := params) neg p.body init.refs
  let read : Reads m compiled.nodes := graphRead m compiled.code compiled.refs val
  let v : View m env read [] (.seq init.code body.code) :=
    ⟨(fun r => nomatch r), (fun r => r), 0, (fun _ _ => (Nat.zero_add _).symm),
      (fun _ bad => by cases bad), graphEquations m env compiled.code compiled.refs solves⟩
  have initial : RealizesOn read (fun r => v.right.embed (body.code.lift r)) init.refs env [] i := by
    intro j agree t slot
    have pAt := Simple.Proofs.param_correct m env (ports params) .nil t slot
    rw [Simple.Proofs.get_select, Simple.Proofs.ports_get] at pAt
    have eq := v.left.straightRead j (init.refs.get slot)
    exact eq.trans pAt
  have output := lowerCorrect neg negSem p.body init.refs v.right i initial exec i (agrees_self [] i) _ p.retvar
  change Tuple.cons (F := fun t => Option (m.Value t)) (read (body.refs.get p.retvar) i) .nil =
    .cons (some value) .nil
  change read (body.refs.get p.retvar) i = some (final.get p.retvar) at output
  rw [output, returned]

theorem whileTraceOfDefined (test : Expr P params .bool) (stmt : Stmt P true params params)
    (ret : Port params t) (neg : P [.bool] .bool) (m : Interpretation.{u,v,w} P)
    (env : Tuple m.Value params)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (guardTotal : ∀ store : Tuple m.Value params, ∃ flag : Bool, test.eval m store = some ⟨flag⟩)
    (stepTotal : ∀ store : Tuple m.Value params, test.eval m store = some ⟨true⟩ →
      ∃ next, Exec m stmt store (some next))
    {val : (translate (whileProgram test stmt ret) neg).Valuation m}
    (solves : (translate (whileProgram test stmt ret) neg).Solves m env val)
    (i : Index (program (whileProgram test stmt ret) neg).nodes.length)
    {value : m.Value t}
    (defined : (translate (whileProgram test stmt ret) neg).observe m val i = .cons (some value) .nil) :
    ∃ k final, WhileTrace m test stmt k env final ∧ final.get ret = value := by
  let compiled := program (whileProgram test stmt ret) neg
  let init := Build.straight (paramNodes (P := P) (params := params) (nodes := []) (ports params))
  let slots := (ports params).map (fun _ r => portLeft (right := init.nodes) r)
  let c := expr (params := params) test slots
  let b := lower (params := params) neg stmt (c.code.liftRefs slots)
  let read : Reads m compiled.nodes := graphRead m compiled.code compiled.refs val
  let code := Code.loop init.refs (.seq c.code b.code) (b.code.lift (c.refs.get .head)) b.refs neg
  let v : View m env read [] (.seq init.code code) :=
    ⟨(fun r => nomatch r), (fun r => r), 0, (fun _ _ => (Nat.zero_add _).symm),
      (fun _ bad => by cases bad), graphEquations m env compiled.code compiled.refs solves⟩
  have entry : RealizesOn read (fun r => v.right.embed (code.lift r)) init.refs env [] i := by
    intro j _ t slot
    have pAt := Simple.Proofs.param_correct m env (ports params) .nil t slot
    rw [Simple.Proofs.get_select, Simple.Proofs.ports_get] at pAt
    exact (v.left.straightRead j (init.refs.get slot)).trans pAt
  let outputs : Tuple (Port compiled.nodes) params := (ports params).map fun _ r => portLeft r
  change Tuple.cons (F := fun t => Option (m.Value t)) (read (outputs.get ret) i) .nil =
    .cons (some value) .nil at defined
  have selected := congrArg (fun xs : Tuple (fun t => Option (m.Value t)) [t] => xs.get .head) defined
  change read (outputs.get ret) i = some value at selected
  unfold outputs at selected
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get] at selected
  obtain ⟨k, final, trace, returned, _, _⟩ :=
    loopTraceOfDefined v.right negSem i (test := test) (stmt := stmt)
      (fun {k store flag} carries testEval j agree =>
        exprRead test slots v.right.inner.left store (carries _ (sampleAgrees v.right agree k)) testEval)
      (fun {k store next} carries step =>
        lowerCorrect neg negSem stmt (c.code.liftRefs slots) v.right.inner.right (i.set v.right.key k)
          (liftRefs c.code (fun r => v.right.inner.left.embed r) carries) step)
      guardTotal stepTotal (agrees_self [] i) entry selected
  exact ⟨k, final, trace, returned⟩

end Silmaril.SSA.PEG.Simple.Structured.Proofs
