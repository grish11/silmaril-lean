module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs
public import Silmaril.SSA.PEG.Simple.Thms

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars ins outs : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1} {m : Interpretation.{u,v,w} P}
variable {env : Tuple m.Value carried} {values : g.Valuation m}

def clock (k : Nat) : Index 1 := fun _ => k

theorem setClock (i : Index 1) (k : Nat) : i.set 0 k = clock k := by
  funext j
  have h : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

def read (values : g.Valuation m) (idx : Index 1) (r : Ref g.sort t) : Option (m.Value t) :=
  r.read m.carrier (values (r.id, idx))

theorem row (solves : g.Solves m env values) (i : Index 1) (r : Ref g.sort t) :
    let node := nodeAt g r
    read values i r = node.label.interpret m env i fun slot j _ => read values j (node.arg slot) := by
  cases r with
  | mk id typed =>
    cases typed
    exact solves (id, i)

def Realizes (values : g.Valuation m) (i : Index 1) (scope : Tuple (Ref g.sort) vars)
    (store : Tuple m.Value vars) : Prop :=
  ∀ t (p : Port vars t), read values i (scope.get p) = some (store.get p)

private theorem operands {scope : Tuple (Ref g.sort) vars} {refs : Tuple (Ref g.sort) ins}
    (reads : Reads scope refs) {idx : Index 1} {store : Tuple m.Value vars}
    (entry : Realizes values idx scope store) :
    collect ins (fun j => read values idx (refs.get (portAt ins j))) =
      reads.args.eval m store := by
  induction reads with
  | nil => rfl
  | @cons t ts r rs p wired tail ih =>
    rw [Reads.args, collect, Args.eval]
    have arg0 : read values idx r = some (store.get p) :=
      wired ▸ entry _ p
    simp only [portAt, Fin.cases_zero, Fin.cases_succ, Tuple.get, Expr.evalLift, arg0, ih]
    cases tail.args.eval m store <;> rfl

private theorem projections {scope : Tuple (Ref g.sort) vars} {refs : Tuple (Ref g.sort) outs}
    (reads : Reads scope refs) {idx : Index 1} {store : Tuple m.Value vars}
    (entry : Realizes values idx scope store) :
    Realizes values idx refs (reads.slots.map fun _ p => store.get p) := by
  induction reads with
  | nil => intro _ p; cases p
  | cons p wired tail ih =>
    intro t q
    cases q with
    | head => exact wired ▸ entry _ p
    | tail q => exact ih _ q

theorem schedule {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (code : Schedule g roots scope) (solves : g.Solves m env values) {idx : Index 1}
    {store : Tuple m.Value vars} {final : Tuple m.Value outs}
    (entry : Realizes values idx scope store) (ran : code.lower.runLoopFree m store = some final) :
    Realizes values idx roots final := by
  induction code with
  | done reads =>
    simp only [Schedule.lower, Stmt.runLoopFree, Option.some.injEq] at ran
    cases ran
    exact projections reads entry
  | bind vertex instr refs _ wired args tail ih =>
    have step := row solves idx (Ref.ofId g.sort vertex)
    let rhs (node : Node P carried (Fin 1) g.sort (g.sort vertex)) :=
      node.label.interpret m env idx fun slot j _ => read values j (node.arg slot)
    change read values idx (Ref.ofId g.sort vertex) = rhs (g.node vertex) at step
    rw [wired] at step
    change read values idx (Ref.ofId g.sort vertex) =
      (collect _ (fun j => read values idx (refs.get (portAt _ j)))).elim none (m.run instr) at step
    rw [operands args entry] at step
    change read values idx (Ref.ofId g.sort vertex) =
      (Expr.op instr args.args).eval m store at step
    simp only [Schedule.lower, Stmt.runLoopFree] at ran
    cases h : (Expr.op instr args.args).eval m store with
    | none => simp [h] at ran
    | some val =>
      simp [h] at ran
      apply ih (store := .cons val store) _ ran
      intro t p
      cases p with
      | head => exact step.trans h
      | tail p => exact entry _ p

variable (cert : Certificate g)

theorem initial (solves : g.Solves m env values) :
    Realizes values (clock 0) cert.descriptor.theta env := by
  intro t p
  rw [row solves (clock 0), cert.boundary.thetaRow]
  change read values (clock 0) (cert.descriptor.initial.get p) = _
  rw [row solves (clock 0), cert.boundary.initialRow]
  rfl

theorem update (solves : g.Solves m env values)
    {k : Nat} {next : Tuple m.Value carried}
    (roots : Realizes values (clock k) cert.descriptor.next next) :
    Realizes values (clock (k + 1)) cert.descriptor.theta next := by
  intro t p
  rw [row solves (clock (k + 1)), cert.boundary.thetaRow]
  change read values ((clock (k + 1)).set 0 k) (cert.descriptor.next.get p) = _
  rw [setClock]
  exact roots t p

theorem exitFlag (solves : g.Solves m env values)
    (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {k : Nat} {b : Bool}
    (guard : read values (clock k) cert.descriptor.guard = some ⟨b⟩) :
    read values (clock k) cert.descriptor.negated = some ⟨!b⟩ := by
  rw [row solves (clock k), cert.boundary.negationRow]
  change (collect [.bool] (fun j => read values (clock k)
    ((Tuple.cons cert.descriptor.guard .nil).get (portAt [.bool] j)))).elim
      none (m.run cert.descriptor.negate) = _
  simp only [collect, portAt, Fin.cases_zero, Tuple.get, guard]
  exact neg b

def flags (cert : Certificate g) (values : g.Valuation m) (k : Nat) : Option Bool :=
  (read values (clock k) cert.descriptor.negated).map ULift.down

theorem pass (solves : g.Solves m env values) (i : Index 1) :
    read values i cert.descriptor.pass = (firstTrue (flags cert values)).map ULift.up := by
  rw [row solves i, cert.boundary.passRow]
  change (firstTrue (fun k => (read values (i.set 0 k) cert.descriptor.negated).map ULift.down)).map
    ULift.up = _
  simp only [setClock]
  rfl

def samples (cert : Certificate g) (values : g.Valuation m) (k : Nat) : Option (m.Value result) :=
  read values (clock k) (cert.descriptor.theta.get cert.descriptor.returnSlot)

theorem observation (solves : g.Solves m env values) (i : Index 1) :
    g.observe m values i = .cons
      ((read values i cert.descriptor.pass).elim none fun k =>
        monotonize (samples cert values) k.down) .nil := by
  unfold Graph.observe
  cases roots : g.roots with
  | cons root rest =>
    cases rest
    change Tuple.cons (F := fun t => Option (m.Value t)) (read values i root) .nil = _
    have h := cert.boundary.evalRow
    rw [roots] at h
    change nodeAt g root = _ at h
    rw [row solves i, h]
    change Tuple.cons (F := fun t => Option (m.Value t))
      ((read values i cert.descriptor.pass).elim none (fun k =>
      monotonize (fun j => read values (i.set 0 j)
        (cert.descriptor.theta.get cert.descriptor.returnSlot)) k.down)) .nil = _
    simp only [setClock]
    rfl

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Proofs
