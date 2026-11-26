module

public import Silmaril.SSA.PEG.Simple.Revert.While.Defs
public import Silmaril.SSA.PEG.Simple.While.Trace
public import Silmaril.SSA.PEG.Rules.Defs

/-! # Checked schedules for single-loop PEG regions

A descriptor names rows by reference. The checker validates the loop boundary and
each slice against the graph. A slice starts with the old carried vector.
Primitive bindings read available operands, and a branch binds the selected
φ value without discarding the inherited store. -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars ins outs : List (Ty Data)} {result t : Ty Data} {n l : Nat}
variable {g : Graph P carried [result] n 1} {sort : Fin n → Ty Data}

def refEq (a b : Ref sort t) : Decidable (a = b) :=
  if h : a.id = b.id then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse (fun eq => h (congrArg Ref.id eq))

def tupleEq : {ins : List (Ty Data)} → (a b : Tuple (Ref sort) ins) → Decidable (a = b)
  | _, .nil, .nil => isTrue rfl
  | _, .cons x xs, .cons y ys =>
    match refEq x y, tupleEq xs ys with
    | isTrue h, isTrue hs => isTrue (by cases h; cases hs; rfl)
    | isFalse h, _ => isFalse (by intro eq; cases eq; exact h rfl)
    | _, isFalse h => isFalse (by intro eq; cases eq; exact h rfl)

def nodeAt (g : Graph P carried [result] n l) (r : Ref g.sort t) :
    Node P carried (Fin l) g.sort t :=
  r.typed ▸ g.node r.id

def nodeEq [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (a b : Node P carried (Fin l) sort t) : Decidable (a = b) := by
  obtain ⟨ins, label, args⟩ := a
  obtain ⟨ins', label', args'⟩ := b
  if hi : ins = ins' then
    subst ins'
    letI := Check.labelEq label label'
    letI := tupleEq args args'
    if hl : label = label' then
      if ha : args = args' then exact isTrue (by cases hl; cases ha; rfl)
      else exact isFalse (by intro eq; cases eq; exact ha rfl)
    else exact isFalse (by intro eq; cases eq; exact hl rfl)
  else exact isFalse (fun eq => hi (congrArg Node.inputs eq))

/-- A typed local slot for every operand, in the graph's operand order. -/
inductive Reads (scope : Tuple (Ref sort) vars) : {ins : List (Ty Data)} →
    Tuple (Ref sort) ins → Type u where
  | nil : Reads scope (.nil)
  | cons {t ts} {r : Ref sort t} {rs : Tuple (Ref sort) ts}
      (slot : Port vars t) (wired : scope.get slot = r) (tail : Reads scope rs) :
      Reads scope (.cons r rs)

def lookup (r : Ref sort t) :
    {vars : List (Ty Data)} → (scope : Tuple (Ref sort) vars) →
    Option {p : Port vars t // scope.get p = r}
  | _, .nil => none
  | _, .cons x xs =>
    if h : x.id = r.id then
      have typed := x.typed.symm.trans ((congrArg sort h).trans r.typed)
      some ⟨typed ▸ Port.head, by
        cases typed
        cases x
        cases r
        cases h
        rfl⟩
    else (lookup r xs).map fun p => ⟨.tail p.val, p.property⟩

def Reads.check (scope : Tuple (Ref sort) vars) :
    {ins : List (Ty Data)} → (refs : Tuple (Ref sort) ins) → Option (Reads scope refs)
  | _, .nil => some .nil
  | _, .cons r rs => do
    let p ← lookup r scope
    return .cons p.val p.property (← check scope rs)

def Reads.slots {scope : Tuple (Ref sort) vars} :
    {ins : List (Ty Data)} → {refs : Tuple (Ref sort) ins} →
    Reads scope refs → Tuple (Port vars) ins
  | _, _, .nil => .nil
  | _, _, .cons p _ tail => .cons p tail.slots

def Reads.args {scope : Tuple (Ref sort) vars} :
    {ins : List (Ty Data)} → {refs : Tuple (Ref sort) ins} →
    Reads scope refs → Args P vars ins
  | _, _, .nil => .nil
  | _, _, .cons p _ tail => .cons (.var p) tail.args

/-- Every binding extends the scope. Only the terminal projection commits
the ordered outputs, so old θ slots remain available throughout a slice.
The branch flag lets primitive-only consumers rule out the φ case. -/
inductive Schedule (g : Graph P carried [result] n l) (allowBranch : Bool) :
    {outs : List (Ty Data)} → Tuple (Ref g.sort) outs →
    {vars : List (Ty Data)} → Tuple (Ref g.sort) vars → Type (max u v) where
  | done {outs : List (Ty Data)} {roots : Tuple (Ref g.sort) outs}
      {vars : List (Ty Data)} {scope : Tuple (Ref g.sort) vars} (reads : Reads scope roots) :
      Schedule g allowBranch roots scope
  | bind {outs : List (Ty Data)} {roots : Tuple (Ref g.sort) outs}
      {vars : List (Ty Data)} {scope : Tuple (Ref g.sort) vars} {ins : List (Ty Data)}
      (i : Fin n) (instr : P ins (g.sort i)) (refs : Tuple (Ref g.sort) ins)
      (fresh : i.val ∉ refNumbers scope)
      (row : g.node i = Node.ofLabel (.op instr) refs)
      (reads : Reads scope refs)
      (tail : Schedule g allowBranch roots (.cons (Ref.ofId g.sort i) scope)) :
      Schedule g allowBranch roots scope
  | branch {outs : List (Ty Data)} {roots : Tuple (Ref g.sort) outs}
      {vars : List (Ty Data)} {scope : Tuple (Ref g.sort) vars}
      (enabled : allowBranch = true) (i : Fin n) (flag : Ref g.sort .bool) (yes no : Ref g.sort (g.sort i))
      (fresh : i.val ∉ refNumbers scope)
      (row : g.node i = Node.ofLabel .phi (.cons flag (.cons yes (.cons no .nil))))
      (test : Port vars .bool) (wired : scope.get test = flag)
      (trueArm : Schedule g allowBranch (.cons yes scope) scope)
      (falseArm : Schedule g allowBranch (.cons no scope) scope)
      (tail : Schedule g allowBranch roots (.cons (Ref.ofId g.sort i) scope)) :
      Schedule g allowBranch roots scope

/-- A defined SIMPLE store gives the values of these PEG rows at one
fixed iteration vector. -/
def Schedule.Realizes {graph : Graph P carried [result] n l} (m : Interpretation.{u,v,w} P)
    (values : graph.Valuation m) (idx : Index l) (scope : Tuple (Ref graph.sort) vars)
    (store : Tuple m.Value vars) : Prop :=
  ∀ t (p : Port vars t), Rules.readRef values (scope.get p) idx = some (store.get p)

/-- Check a primitive prefix, and construct its continuation in the resulting scope. -/
def Schedule.checkThen (g : Graph P carried [result] n l) {allowBranch : Bool} (roots : Tuple (Ref g.sort) outs)
    (finish : ∀ {vars : List (Ty Data)} (scope : Tuple (Ref g.sort) vars),
      Option (Schedule g allowBranch roots scope)) :
    (order : List (Fin n)) → {vars : List (Ty Data)} → (scope : Tuple (Ref g.sort) vars) →
    Option (Schedule g allowBranch roots scope)
  | [], _, scope => finish scope
  | i :: rest, _, scope =>
    if fresh : i.val ∉ refNumbers scope then
      match row : g.node i with
      | ⟨_, .op instr, refs⟩ =>
        match Reads.check scope refs with
        | none => none
        | some reads =>
          (checkThen g roots finish rest (.cons (Ref.ofId g.sort i) scope)).map
            (.bind i instr refs fresh row reads)
      | _ => none
    else none

def Schedule.check (g : Graph P carried [result] n l) (roots : Tuple (Ref g.sort) outs)
    (order : List (Fin n)) (scope : Tuple (Ref g.sort) vars)
    (allowBranch : Bool := false) : Option (Schedule g allowBranch roots scope) :=
  checkThen g roots (fun scope => (Reads.check scope roots).map .done) order scope

def Schedule.lower {g : Graph P carried [result] n l} {allowBranch : Bool} :
    {outs : List (Ty Data)} → {roots : Tuple (Ref g.sort) outs} →
    {vars : List (Ty Data)} → {scope : Tuple (Ref g.sort) vars} →
    Schedule g allowBranch roots scope → Stmt P false vars outs
  | _, _, _, _, .done reads => .project reads.slots
  | _, _, _, _, .bind _ instr _ _ _ reads tail => .seq (.assign (.op instr reads.args)) tail.lower
  | _, _, _, _, .branch _ _ _ _ _ _ _ test _ yes no tail =>
    .seq (.branch (.var test) yes.lower no.lower) tail.lower

/-- Untrusted row references for a loop boundary. Each carried position
is initialized by its corresponding input parameter. In invariant mode,
`theta` and `next` may both name that parameter. The body commits all
next values simultaneously, and the exit samples one current value. -/
structure Descriptor (g : Graph P carried [result] n 1) where
  theta : Tuple (Ref g.sort) carried
  initial : Tuple (Ref g.sort) carried
  next : Tuple (Ref g.sort) carried
  guard : Ref g.sort .bool
  negated : Ref g.sort .bool
  negate : P [.bool] .bool
  pass : Ref g.sort .count
  returnSlot : Port carried result

/-- Untrusted scheduling evidence for the two slices and for unbounded PEG demands. -/
structure Plan (n : Nat) where
  guardOrder : List (Fin n)
  bodyOrder : List (Fin n)
  rank : DemandRank n 1

def Descriptor.guardRoots (d : Descriptor g) : Tuple (Ref g.sort) (.bool :: carried) :=
  .cons d.guard d.theta

abbrev Descriptor.FeedbackSlot (d : Descriptor g) (p : Port carried t) : Prop :=
  nodeAt g (d.theta.get p) =
    .ofLabel (.theta 0) (.cons (d.initial.get p) (.cons (d.next.get p) .nil))

def Descriptor.InvariantSlot (d : Descriptor g) (p : Port carried t) : Prop :=
  d.theta.get p = d.initial.get p ∧ d.next.get p = d.initial.get p

abbrev Descriptor.Slot (d : Descriptor g) (allowInvariant : Bool) (p : Port carried t) : Prop :=
  if allowInvariant then d.FeedbackSlot p ∨ d.InvariantSlot p else d.FeedbackSlot p

/-- Port-indexed structural evidence, independent of the executable checker. -/
structure Boundary (g : Graph P carried [result] n 1) (d : Descriptor g)
    (allowInvariant : Bool := false) : Prop where
  parentless : g.forest.parent 0 = none
  initialRow : ∀ t (p : Port carried t),
    nodeAt g (d.initial.get p) = .ofLabel (.param p) .nil
  thetaRow : ∀ t (p : Port carried t), d.Slot allowInvariant p
  negationRow : nodeAt g d.negated = .ofLabel (.op d.negate) (.cons d.guard .nil)
  passRow : nodeAt g d.pass = .ofLabel (.pass 0) (.cons d.negated .nil)
  evalRow : nodeAt g (g.roots.get .head) =
    .ofLabel (.eval 0) (.cons (d.theta.get d.returnSlot) (.cons d.pass .nil))

theorem Boundary.slotCases {d : Descriptor g} {allowInvariant : Bool}
    (b : Boundary g d allowInvariant) (p : Port carried t) :
    d.FeedbackSlot p ∨ d.InvariantSlot p := by
  cases allowInvariant
  · exact .inl (b.thetaRow _ p)
  · exact b.thetaRow _ p

structure Certificate (g : Graph P carried [result] n 1) (allowInvariant : Bool := false)
    (allowBranch : Bool := false) where
  descriptor : Descriptor g
  boundary : Boundary g descriptor allowInvariant
  rank : DemandRank n 1
  ranked : rank.check g = true
  guard : Schedule g allowBranch descriptor.guardRoots descriptor.theta
  update : Schedule g allowBranch descriptor.next descriptor.theta

def allPorts : (vars : List (Ty Data)) →
    (F : ∀ {t}, Port vars t → Prop) → (∀ t p, Decidable (@F t p)) →
    Decidable (∀ t p, @F t p)
  | [], _, _ => isTrue (by intro _ p; cases p)
  | t :: vars, F, dec =>
    match dec t .head with
    | isFalse no => isFalse (fun yes => no (yes t .head))
    | isTrue head =>
      match allPorts vars (fun p => F (.tail p)) (fun t p => dec t (.tail p)) with
      | isFalse no => isFalse (fun yes => no fun t p => yes t (.tail p))
      | isTrue tail =>
        isTrue (by intro t p; cases p with | head => exact head | tail p => exact tail t p)

structure CheckedBoundary (g : Graph P carried [result] n 1)
    (d : Descriptor g) (allowInvariant : Bool) : Type where
  valid : Boundary g d allowInvariant

/-- Check structural wiring independently of the choice of scheduler. -/
def checkBoundary [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) (d : Descriptor g)
    (allowInvariant : Bool) : Option (CheckedBoundary g d allowInvariant) :=
  letI : ∀ t, DecidableEq (Node P carried (Fin 1) g.sort t) := fun _ => nodeEq
  letI : ∀ t, DecidableEq (Ref g.sort t) := fun _ => refEq
  letI : Decidable (∀ t (p : Port carried t),
      nodeAt g (d.initial.get p) = .ofLabel (.param p) .nil) :=
    allPorts carried _ (fun _ _ => nodeEq _ _)
  letI : Decidable (∀ t (p : Port carried t), d.Slot allowInvariant p) :=
    allPorts carried _ (fun _ _ => by
      unfold Descriptor.Slot Descriptor.FeedbackSlot Descriptor.InvariantSlot
      infer_instance)
  if parentless : g.forest.parent 0 = none then
    if initial : ∀ t (p : Port carried t),
        nodeAt g (d.initial.get p) = .ofLabel (.param p) .nil then
      if slots : ∀ t (p : Port carried t), d.Slot allowInvariant p then
        if negation : nodeAt g d.negated = .ofLabel (.op d.negate) (.cons d.guard .nil) then
          if pass : nodeAt g d.pass = .ofLabel (.pass 0) (.cons d.negated .nil) then
            if eval : nodeAt g (g.roots.get .head) =
                .ofLabel (.eval 0) (.cons (d.theta.get d.returnSlot) (.cons d.pass .nil)) then
              some ⟨⟨parentless, initial, slots, negation, pass, eval⟩⟩
            else none
          else none
        else none
      else none
    else none
  else none

/-- Check the supplied boundary and retain its identity in the certificate. -/
def checkWith [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) (d : Descriptor g) (plan : Plan n)
    (allowInvariant : Bool) : Option {cert : Certificate g allowInvariant // cert.descriptor = d} := do
  let some boundary := checkBoundary g d allowInvariant | none
  if ranked : plan.rank.check g = true then
    let guard ← Schedule.check g d.guardRoots plan.guardOrder d.theta
    let update ← Schedule.check g d.next plan.bodyOrder d.theta
    return ⟨⟨d, boundary.valid, plan.rank, ranked, guard, update⟩, rfl⟩
  else none

def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) (d : Descriptor g) (plan : Plan n) : Option (Certificate g) :=
  (checkWith g d plan false).map Subtype.val

/-- Collect a primitive slice in reverse topological order. Carried rows
are leaves, and a completed binding is reused by later visits. Fuel
bounds the depth of the search, including cyclic proposals. -/
def visit (g : Graph P carried [result] n l) (carriedRows : List Nat) :
    Nat → Fin n → List (Fin n) → Option (List (Fin n))
  | fuel, i, order =>
    if i.val ∈ carriedRows ∨ i ∈ order then some order
    else
      match fuel with
      | 0 => none
      | fuel + 1 =>
        let node := g.node i
        match node.label with
        | .op _ => do
          let prior ← (List.finRange node.inputs.length).foldlM
            (fun acc slot => visit g carriedRows fuel (node.arg slot).id acc) order
          return i :: prior
        | _ => none
termination_by structural fuel _ _ => fuel

/-- Infer a scope-closed order for a primitive slice of a PEG. -/
def scopedOrder (g : Graph P carried [result] n l) (scope : Tuple (Ref g.sort) vars)
    (roots : Tuple (Ref g.sort) outs) : Option (List (Fin n)) := do
  let order ← (refNumbers roots).foldlM (fun order i => do
    if bound : i < n then visit g (refNumbers scope) n ⟨i, bound⟩ order else none) []
  return order.reverse

def sliceOrder (g : Graph P carried [result] n 1) (d : Descriptor g)
    (roots : Tuple (Ref g.sort) outs) : Option (List (Fin n)) :=
  scopedOrder g d.theta roots

/-- Synthesize both slice orders from a supplied typed boundary, then
validate the complete certificate. Boundary discovery and demand-rank
synthesis are separate. -/
def checkScheduledWith [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) (d : Descriptor g) (rank : DemandRank n 1)
    (allowInvariant : Bool) : Option {cert : Certificate g allowInvariant // cert.descriptor = d} := do
  let some guard := sliceOrder g d d.guardRoots | none
  let some body := sliceOrder g d d.next | none
  checkWith g d ⟨guard, body, rank⟩ allowInvariant

def checkScheduled [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) (d : Descriptor g) (rank : DemandRank n 1) :
    Option (Certificate g) :=
  (checkScheduledWith g d rank false).map Subtype.val

variable {allowInvariant allowBranch : Bool}

/-- The loop store caches the continuation guard with the carried vector.
The preheader computes it once, and each successful step prepares the guard
for the next iteration. Temporaries in each slice are projected away. -/
def Certificate.body (cert : Certificate g allowInvariant allowBranch) :
    Stmt P false (.bool :: carried) (.bool :: carried) :=
  .seq (.project ((ports carried).map fun _ p => .tail p))
    (.seq cert.update.lower cert.guard.lower)

def Certificate.revert (cert : Certificate g allowInvariant allowBranch) : Program P true carried result :=
  ⟨.bool :: carried,
    .seq cert.guard.lower.enableWhile (.while rfl (.var .head) cert.body.enableWhile),
    .tail cert.descriptor.returnSlot⟩

/-- A finite exit in both semantics. The first-pass count is the trace
length, and every earlier sample of the observed θ is defined. -/
structure Certificate.ExitWitness (cert : Certificate g allowInvariant allowBranch) (m : Interpretation.{u,v,w} P)
    (values : g.Valuation m) (idx : Index 1) (k : Nat)
    (start final : Tuple m.Value (.bool :: carried)) (value : m.Value result) : Prop where
  trace : WhileTrace m (.var .head) cert.body.enableWhile k start final
  returned : final.get (.tail cert.descriptor.returnSlot) = value
  pass : cert.descriptor.pass.read m.carrier (values (cert.descriptor.pass.id, idx)) = some ⟨k⟩
  sample : let ref := cert.descriptor.theta.get cert.descriptor.returnSlot
    ref.read m.carrier (values (ref.id, fun _ => k)) = some value
  definedBefore : ∀ j < k, let ref := cert.descriptor.theta.get cert.descriptor.returnSlot
    (ref.read m.carrier (values (ref.id, fun _ => j))).isSome

/-- One pass count for the entire carried boundary of a successful trace.
Every carried sample is defined throughout the Figure 11 eval prefix. -/
structure Certificate.TraceObservation (cert : Certificate g allowInvariant allowBranch)
    (m : Interpretation.{u,v,w} P) (values : g.Valuation m) (idx : Index 1) (k : Nat)
    (final : Tuple m.Value (.bool :: carried)) : Prop where
  pass : cert.descriptor.pass.read m.carrier (values (cert.descriptor.pass.id, idx)) = some ⟨k⟩
  sample : ∀ t (p : Port carried t), let ref := cert.descriptor.theta.get p
    ref.read m.carrier (values (ref.id, fun _ => k)) = some (final.get (.tail p))
  definedBefore : ∀ j < k, ∀ t (p : Port carried t), let ref := cert.descriptor.theta.get p
    (ref.read m.carrier (values (ref.id, fun _ => j))).isSome

/-- The guard schedule and the entire update vector must succeed on every
defined old store. The interpretation makes the operations pure. -/
structure Certificate.Total (cert : Certificate g allowInvariant allowBranch) (m : Interpretation.{u,v,w} P) : Prop where
  guard : ∀ store, ∃ tagged, cert.guard.lower.runLoopFree m store = some tagged
  update : ∀ store, ∃ next, cert.update.lower.runLoopFree m store = some next

def Certificate.runFrom (cert : Certificate g allowInvariant allowBranch) (m : Interpretation.{u,v,w} P) :
    Nat → Tuple m.Value (.bool :: carried) → Option (m.Value result)
  | fuel, .cons flag store =>
    if flag.down then
      match fuel with
      | 0 => none
      | k + 1 => (cert.body.runLoopFree m (.cons flag store)).bind (cert.runFrom m k)
    else some (store.get cert.descriptor.returnSlot)
termination_by structural fuel _ => fuel

/-- Run the emitted structured program with a bound on successful body steps. -/
def Certificate.runFuel (cert : Certificate g allowInvariant allowBranch) (m : Interpretation.{u,v,w} P)
    (fuel : Nat) (input : Tuple m.Value carried) : Option (m.Value result) :=
  (cert.guard.lower.runLoopFree m input).bind (cert.runFrom m fuel)

end Silmaril.SSA.PEG.Simple.Revert.While.Region
