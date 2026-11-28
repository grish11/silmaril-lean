module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Defs
public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Views

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Simple.Proofs (NodeValues eval_append eval_lift realizes_lift get_map get_select)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {vars outs params before : List (Ty Data)} {t : Ty Data}
variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

mutual

theorem exprExact {t : Ty Data} (rhs : Expr P vars t) {before : List (Ty Data)}
    (ctx : Tuple (Port before) vars)
    (values : NodeValues (model m) before) (store : Tuple m.Value vars)
    (entry : Realizes (model m) values ctx store) :
    let b := (expr rhs).lower (params := params) ctx
    (b.code.eval (model m) env values).get (b.refs.get .head) = rhs.eval m store := by
  cases rhs with
  | var p => exact entry _ p
  | op op args =>
    let b := (arguments args).lower (params := params) ctx
    change (collect _ (fun slot => (b.code.eval (model m) env values).get
      (b.refs.get (portAt _ slot)))).elim none (m.run op) = (args.eval m store).elim none (m.run op)
    rw [argsExact args ctx values store entry]

theorem argsExact {outs : List (Ty Data)} (args : Args P vars outs) {before : List (Ty Data)}
    (ctx : Tuple (Port before) vars)
    (values : NodeValues (model m) before) (store : Tuple m.Value vars)
    (entry : Realizes (model m) values ctx store) :
    let b := (arguments args).lower (params := params) ctx
    collect outs (fun slot => (b.code.eval (model m) env values).get
      (b.refs.get (portAt outs slot))) = args.eval m store := by
  cases args with
  | nil => rfl
  | @cons t ts rhs rest =>
    let head := (expr rhs).lower (params := params) ctx
    let tail := (arguments rest).lower (params := params) (head.code.liftRefs ctx)
    let vs := head.code.eval (model m) env values
    let vs' := tail.code.eval (model m) env vs
    change collect (t :: ts) (fun slot =>
      ((head.code.append tail.code).eval (model m) env values).get
        ((Tuple.cons (tail.code.lift (head.refs.get .head)) tail.refs).get (portAt _ slot))) = _
    rw [eval_append]
    simp only [collect, portAt, Fin.cases_zero, Fin.cases_succ, Tuple.get]
    rw [show vs'.get (tail.code.lift (head.refs.get .head)) = rhs.eval m store from
      (eval_lift _ _ _ _ _).trans (exprExact rhs ctx values store entry)]
    rw [show collect ts (fun slot => vs'.get (tail.refs.get (portAt ts slot))) =
        rest.eval m store from
      argsExact rest (head.code.liftRefs ctx) vs store
        (realizes_lift (model m) env head.code entry)]
    simp only [Args.eval, Expr.eval]
    cases (rhs.evalLift m store).down <;> cases rest.eval m store <;> rfl

end

theorem sourceOfStmt (stmt : Stmt P false vars outs) : (Body.ofStmt stmt).source = stmt := by
  induction stmt with
  | assign _ | project _ => rfl
  | seq _ _ first second => simp only [Body.ofStmt, Body.source, first, second]
  | branch _ _ _ yes no => simp only [Body.ofStmt, Body.source, yes, no]
  | «while» impossible _ _ _ => cases impossible

theorem phiRead (flag : Port before .bool)
    (yes no : Tuple (Port before) outs) (values : NodeValues (model m) before)
    (slot : Port outs t) :
    let joined := phiNodes (P := Opcode P) (params := params) flag yes no
    (joined.code.eval (model m) env values).get (joined.refs.get slot) =
      (values.get flag).elim none (fun b =>
        values.get (if b.down then yes.get slot else no.get slot)) := by
  induction slot with
  | head =>
    cases yes with
    | cons y ys =>
      cases no with
      | cons n ns =>
        let rest := phiNodes (P := Opcode P) (params := params) flag ys ns
        let v := rest.code.eval (model m) env values
        change (v.get (rest.code.lift flag)).elim none
          (fun b => if b.down then v.get (rest.code.lift y) else v.get (rest.code.lift n)) =
          (values.get flag).elim none (fun b => values.get (if b.down then y else n))
        simp only [v, eval_lift]
        cases values.get flag with
        | none => rfl
        | some b =>
          obtain ⟨b⟩ := b
          cases b <;> rfl
  | tail slot ih =>
    cases yes with
    | cons y ys =>
      cases no with
      | cons n ns =>
        let rest := phiNodes (P := Opcode P) (params := params) flag ys ns
        change (Tuple.cons _ (rest.code.eval (model m) env values)).get
          ((rest.refs.map fun _ p => Port.tail p).get slot) =
          (values.get flag).elim none (fun b => values.get (if b.down then ys.get slot else ns.get slot))
        rw [get_map]
        exact ih ys ns

private theorem branchRead (test : Simple.Build (Opcode P) params before [.bool])
    (yes : Simple.Build (Opcode P) params test.nodes outs)
    (no : Simple.Build (Opcode P) params yes.nodes outs)
    (values : NodeValues (model m) before) (slot : Port outs t) :
    let flag := no.code.lift (yes.code.lift (test.refs.get .head))
    let joined := phiNodes flag (no.code.liftRefs yes.refs) no.refs
    let testValues := test.code.eval (model m) env values
    let yesValues := yes.code.eval (model m) env testValues
    let noValues := no.code.eval (model m) env yesValues
    ((test.code.append (yes.code.append (no.code.append joined.code))).eval
      (model m) env values).get (joined.refs.get slot) =
      (testValues.get (test.refs.get .head)).elim none
        (fun b => if b.down then yesValues.get (yes.refs.get slot) else noValues.get (no.refs.get slot)) := by
  dsimp only
  rw [eval_append, eval_append, eval_append, phiRead, eval_lift, eval_lift]
  simp only [Simple.Code.liftRefs, get_map]
  cases (test.code.eval (model m) env values).get (test.refs.get .head) with
  | none => rfl
  | some b =>
    obtain ⟨b⟩ := b
    cases b with
    | false => rfl
    | true => exact eval_lift _ _ _ _ _

private theorem afterEquation (token : Port before .bool) (value : Port before t)
    (vs : NodeValues (model m) before) :
    emitValue (model m) env (.op (.after t)) (.cons token (.cons value .nil)) vs =
      (vs.get value).bind (fun _ => vs.get token) := by
  change (collect [.bool, t] _).elim none _ = _
  simp only [collect, portAt, Fin.cases_zero, Fin.cases_succ, Tuple.get]
  cases vs.get token <;> cases vs.get value <;> rfl

/-- A bottom incoming token cannot be restored by a following statement. -/
theorem bodyBottom (body : Body P vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (values : NodeValues (model m) before) (bottom : values.get (ctx.get .head) = none) :
    let b := body.lower (params := params) ctx
    (b.code.eval (model m) env values).get (b.refs.get .head) = none := by
  induction body generalizing before with
  | @assign vars t rhs =>
    let e := (expr rhs).lower (params := params) (tail ctx)
    let vs := e.code.eval (model m) env values
    change emitValue (model m) env (.op (.after t)) (.cons (e.code.lift (ctx.get .head)) e.refs) vs = none
    cases h : e.refs with
    | cons value rest =>
      cases rest
      rw [afterEquation]
      change (vs.get value).bind (fun _ => vs.get (e.code.lift (ctx.get .head))) = _
      rw [show vs.get (e.code.lift (ctx.get .head)) = none from (eval_lift _ _ _ _ _).trans bottom]
      cases vs.get value <;> rfl
  | project slots => exact bottom
  | seq first second ihFirst ihSecond =>
    let a := first.lower (params := params) ctx
    let b := second.lower (params := params) a.refs
    change ((a.code.append b.code).eval (model m) env values).get (b.refs.get .head) = none
    rw [eval_append]
    exact ihSecond a.refs _ (ihFirst ctx values bottom)
  | branch guard yes no ihYes ihNo =>
    let test := (expr guard).lower (params := params) (tail ctx)
    let initial := test.code.liftRefs ctx
    let y := yes.lower (params := params) initial
    let n := no.lower (params := params) (y.code.liftRefs initial)
    let testValues := test.code.eval (model m) env values
    let yesValues := y.code.eval (model m) env testValues
    have initialBottom : testValues.get (initial.get .head) = none := by
      simpa only [testValues, initial, Simple.Code.liftRefs, get_map, eval_lift] using bottom
    have noBottom : yesValues.get ((y.code.liftRefs initial).get .head) = none := by
      simpa only [yesValues, Simple.Code.liftRefs, get_map, eval_lift] using initialBottom
    have yBottom := ihYes initial testValues initialBottom
    have nBottom := ihNo (y.code.liftRefs initial) yesValues noBottom
    have joined := branchRead m env test y n values .head
    simp only [Body.lower, Simple.Build.thenBuild]
    rw [joined]
    cases testValues.get (test.refs.get .head) with
    | none => rfl
    | some b =>
      obtain ⟨b⟩ := b
      cases b with
      | false => exact nBottom
      | true => exact yBottom

/-- With a realized input store, the lowered slice produces a token just
when the complete source slice succeeds, and preserves all output slots. -/
theorem bodyExact (body : Body P vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (values : NodeValues (model m) before) (token : (model m).Value .bool)
    (store : Tuple m.Value vars) (entry : Realizes (model m) values ctx (.cons token store)) :
    let b := body.lower (params := params) ctx
    let result := b.code.eval (model m) env values
    match body.source.runLoopFree m store with
    | none => result.get (b.refs.get .head) = none
    | some next => Realizes (model m) result b.refs (.cons token next) := by
  induction body generalizing before with
  | @assign vars t rhs =>
    cases ctx with
    | cons incoming ctx =>
      let e := (expr rhs).lower (params := params) ctx
      let vs := e.code.eval (model m) env values
      have rhsValue := exprExact m env rhs ctx values store (fun t p => entry t (.tail p))
      have oldValue : vs.get (e.code.lift incoming) = some token :=
        (eval_lift _ _ _ _ _).trans (entry _ .head)
      have flat : e.refs = .cons (e.refs.get .head) .nil := by
        cases e.refs with
        | cons _ rest => cases rest; rfl
      let nxt := emitValue (model m) env (.op (.after t)) (.cons (e.code.lift incoming) e.refs) vs
      have nextToken : nxt = (rhs.eval m store).map (fun _ => token) := by
        change emitValue _ _ _ _ _ = _
        rw [flat, afterEquation, oldValue]
        change (vs.get (e.refs.get .head)).bind (fun _ => some token) = _
        rw [rhsValue]
        cases rhs.eval m store <;> rfl
      simp only [Body.source, Stmt.runLoopFree, Body.lower, Token.tail, Tuple.get, Simple.Code.eval]
      cases test : rhs.eval m store with
      | none =>
        change nxt = none
        simpa only [test, Option.map_none] using nextToken
      | some value =>
        intro ty slot
        cases slot with
        | head =>
          change nxt = some token
          simpa only [test, Option.map_some] using nextToken
        | tail slot =>
          cases slot with
          | head => exact rhsValue.trans test
          | tail slot =>
            change (Tuple.cons (F := fun t => Option ((model m).Value t)) nxt vs).get
              (((e.code.liftRefs ctx).map fun _ p => Port.tail p).get slot) = some (store.get slot)
            rw [get_map]
            change vs.get ((e.code.liftRefs ctx).get slot) = _
            simp only [vs, Simple.Code.liftRefs, get_map, eval_lift]
            exact entry _ (.tail slot)
  | project slots =>
    cases ctx with
    | cons incoming ctx =>
      change Realizes (model m) values (.cons incoming (select ctx slots))
        (.cons token (select store slots))
      intro t p
      cases p with
      | head => exact entry _ .head
      | tail p =>
        change values.get ((select ctx slots).get p) = some ((select store slots).get p)
        rw [get_select, get_select]
        exact entry _ (.tail (slots.get p))
  | seq first second ihFirst ihSecond =>
    let a := first.lower (params := params) ctx
    let b := second.lower (params := params) a.refs
    let vs := a.code.eval (model m) env values
    simp only [Body.source, Stmt.runLoopFree, Body.lower, Simple.Build.thenBuild]
    rw [eval_append]
    have aExact := ihFirst ctx values store entry
    cases result : first.source.runLoopFree m store with
    | none =>
      exact bodyBottom m env second a.refs vs (by simpa only [result] using aExact)
    | some next =>
      exact ihSecond a.refs vs next (by simpa only [result] using aExact)
  | @branch vars outs guard yes no ihYes ihNo =>
    let test := (expr guard).lower (params := params) (tail ctx)
    let initial := test.code.liftRefs ctx
    let y := yes.lower (params := params) initial
    let n := no.lower (params := params) (y.code.liftRefs initial)
    let testValues := test.code.eval (model m) env values
    let yesValues := y.code.eval (model m) env testValues
    have testResult : testValues.get (test.refs.get .head) = guard.eval m store :=
      exprExact m env guard (tail ctx) values store (by
        cases ctx with
        | cons _ _ => exact fun ty slot => entry ty (.tail slot))
    have initialStore : Realizes (model m) testValues initial (.cons token store) :=
      realizes_lift (model m) env test.code entry
    have noStore : Realizes (model m) yesValues (y.code.liftRefs initial) (.cons token store) :=
      realizes_lift (model m) env y.code initialStore
    have yExact := ihYes initial testValues store initialStore
    have nExact := ihNo (y.code.liftRefs initial) yesValues store noStore
    have read ty (slot : Port (.bool :: outs) ty) := (branchRead m env test y n values slot).trans
      (congrArg (fun condition => condition.elim none (fun b =>
        if b.down then yesValues.get (y.refs.get slot)
        else (n.code.eval (model m) env yesValues).get (n.refs.get slot))) testResult)
    simp only [Body.source, Stmt.runLoopFree, Body.lower, Simple.Build.thenBuild]
    cases selected : guard.eval m store with
    | none =>
      simpa only [selected, Option.bind_none, Option.elim_none] using read _ .head
    | some b =>
      obtain ⟨b⟩ := b
      cases b
      · simp only [Option.bind_some]
        cases arm : no.source.runLoopFree m store with
        | none =>
          rw [arm] at nExact
          exact (read _ .head).trans (by rw [selected]; exact nExact)
        | some next =>
          rw [arm] at nExact
          intro ty slot
          exact (read ty slot).trans (by rw [selected]; exact nExact ty slot)
      · simp only [Option.bind_some, ↓reduceIte]
        cases arm : yes.source.runLoopFree m store with
        | none =>
          rw [arm] at yExact
          exact (read _ .head).trans (by rw [selected]; exact yExact)
        | some next =>
          rw [arm] at yExact
          intro ty slot
          exact (read ty slot).trans (by rw [selected]; exact yExact ty slot)

end Silmaril.SSA.PEG.Simple.Structured.Token.Proofs
