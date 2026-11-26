module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Parameters.Defs

/-! # Parentless single loops with ordered observations

The initializer reads typed external parameters. The guard and simultaneous
update read old θ slots and the same retained parameters. One checked
zero-based unit counter represents the pass count. The exit schedule may
read parameters, the shared pass, and samples of the carried slots.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params carried results : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P params results n 1}

abbrev nodeAt (g : Graph P params results n 1) (ref : Ref g.sort t) :
    Node P params (Fin 1) g.sort t :=
  ref.typed ▸ g.node ref.id

inductive Readout (carried : List (Ty Data)) : Ty Data → Type u
  | eval {t : Ty Data} (slot : Port carried t) : Readout carried t
  | pass : Readout carried .count

structure Descriptor (g : Graph P params results n 1) (carried : List (Ty Data)) where
  theta : Tuple (Ref g.sort) carried
  initial : Tuple (Ref g.sort) carried
  next : Tuple (Ref g.sort) carried
  exit : Ref g.sort .bool
  pass : Ref g.sort .count
  clock : Port carried .count
  zero : P [] .count
  tick : P [.count] .count
  negate : P [.bool] .bool
  samples : List (Ty Data)
  sampleRefs : Tuple (Ref g.sort) samples
  outputs : Tuple (Readout carried) samples

/-- The scalar view is used only to reuse the existing typed scheduler.
Its ordered outputs play no role in the unchanged row equations. -/
abbrev Descriptor.view (d : Descriptor g carried) : Graph P params [.count] n 1 :=
  g.withRoots (.cons d.pass .nil)

abbrev Descriptor.tagged (d : Descriptor g carried) : Tuple (Ref g.sort) (.bool :: carried) :=
  .cons d.exit d.theta

def Descriptor.slot (d : Descriptor g carried) : Readout carried t → Port (.bool :: carried) t
  | .eval slot => .tail slot
  | .pass => .tail d.clock

def Descriptor.slots (d : Descriptor g carried) : Tuple (Port (.bool :: carried)) d.samples :=
  d.outputs.map fun _ r => d.slot r

def Descriptor.rootRow (d : Descriptor g carried) (root : Ref g.sort t) :
    Readout carried t → Prop
  | .eval slot => nodeAt g root = .ofLabel (.eval 0)
      (.cons (d.theta.get slot) (.cons d.pass .nil))
  | .pass => root = d.pass

structure Boundary (d : Descriptor g carried) : Prop where
  parentless : g.forest.parent 0 = none
  theta : ∀ t (p : Port carried t),
    nodeAt g (d.theta.get p) = .ofLabel (.theta 0) (.cons (d.initial.get p) (.cons (d.next.get p) .nil))
  pass : nodeAt g d.pass = .ofLabel (.pass 0) (.cons d.exit .nil)
  zero : nodeAt g (d.initial.get d.clock) = .ofLabel (.op d.zero) .nil
  tick : nodeAt g (d.next.get d.clock) = .ofLabel (.op d.tick) (.cons (d.theta.get d.clock) .nil)
  outputs : ∀ t (p : Port d.samples t), d.rootRow (d.sampleRefs.get p) (d.outputs.get p)

structure Accepted (g : Graph P params results n 1) (carried : List (Ty Data)) where
  descriptor : Descriptor g carried
  boundary : Boundary descriptor
  rank : DemandRank n 1
  ranked : rank.check g = true
  captures : Parameters descriptor.view
  start : Schedule descriptor.view false
    (appendScope descriptor.initial captures.refs) captures.refs
  guard : Schedule descriptor.view false
    (appendScope descriptor.tagged captures.refs) (appendScope descriptor.theta captures.refs)
  step : Schedule descriptor.view false
    (appendScope descriptor.next captures.refs) (appendScope descriptor.theta captures.refs)
  finish : Schedule descriptor.view false g.roots (appendScope descriptor.sampleRefs captures.refs)

/-- All observed evals must reference the same pass row. The checker
also validates which old-store slot can represent that pass count. -/
def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n 1) (d : Descriptor g carried) (rank : DemandRank n 1) :
    Option {a : Accepted g carried // a.descriptor = d} := do
  letI : ∀ t, DecidableEq (Node P params (Fin 1) g.sort t) := fun _ => nodeEq
  letI : Decidable (∀ t (p : Port carried t),
      nodeAt g (d.theta.get p) =
        .ofLabel (.theta 0) (.cons (d.initial.get p) (.cons (d.next.get p) .nil))) :=
    allPorts carried _ (fun _ _ => nodeEq _ _)
  letI : Decidable (∀ t (p : Port d.samples t), d.rootRow (d.sampleRefs.get p) (d.outputs.get p)) :=
    allPorts d.samples _ (fun _ p => by
      generalize d.outputs.get p = out
      cases out with
      | eval slot =>
        exact nodeEq (nodeAt g (d.sampleRefs.get p)) (.ofLabel (.eval 0)
          (.cons (d.theta.get slot) (.cons d.pass .nil)))
      | pass => exact refEq (d.sampleRefs.get p) d.pass)
  if valid : g.forest.parent 0 = none ∧
      (∀ t (p : Port carried t), nodeAt g (d.theta.get p) =
        .ofLabel (.theta 0) (.cons (d.initial.get p) (.cons (d.next.get p) .nil))) ∧
      nodeAt g d.pass = .ofLabel (.pass 0) (.cons d.exit .nil) ∧
      nodeAt g (d.initial.get d.clock) = .ofLabel (.op d.zero) .nil ∧
      nodeAt g (d.next.get d.clock) = .ofLabel (.op d.tick) (.cons (d.theta.get d.clock) .nil) ∧
      (∀ t (p : Port d.samples t), d.rootRow (d.sampleRefs.get p) (d.outputs.get p)) ∧
      rank.check g = true then do
    let captures := Parameters.infer d.view
    let retained := captures.refs
    let old := appendScope d.theta retained
    let start ← Schedule.inferPrimitive d.view retained (appendScope d.initial retained)
    let guard ← Schedule.inferPrimitive d.view old (appendScope d.tagged retained)
    let step ← Schedule.inferPrimitive d.view old (appendScope d.next retained)
    let finish ← Schedule.inferPrimitive d.view (appendScope d.sampleRefs retained) g.roots
    return ⟨⟨d, ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2.1,
      valid.2.2.2.2.2.1⟩, rank, valid.2.2.2.2.2.2, captures, start, guard, step, finish⟩, rfl⟩
  else none

def oldSlots (carried : List (Ty Data)) : Tuple (Port (.bool :: carried)) carried :=
  (ports carried).map fun _ p => .tail p

abbrev Accepted.storeTypes (a : Accepted g carried) :=
  .bool :: (carried ++ a.captures.types)

def Accepted.startCode (a : Accepted g carried) : Stmt P false params a.storeTypes :=
  .seq (.project a.captures.inputs) (.seq a.start.lower a.guard.lower)

def Accepted.test (a : Accepted g carried) : Expr P a.storeTypes .bool :=
  .op a.descriptor.negate (.cons (.var .head) .nil)

def Accepted.body (a : Accepted g carried) : Stmt P false a.storeTypes a.storeTypes :=
  .seq (.project (oldSlots (carried ++ a.captures.types))) (.seq a.step.lower a.guard.lower)

def Accepted.exitSlots (a : Accepted g carried) :
    Tuple (Port a.storeTypes) (a.descriptor.samples ++ a.captures.types) :=
  appendScope
    (a.descriptor.slots.map fun _ p => portLeft p)
    ((ports a.captures.types).map fun _ p => .tail (portRight carried p))

def Accepted.finishCode (a : Accepted g carried) : Stmt P false a.storeTypes results :=
  .seq (.project a.exitSlots) a.finish.lower

/-- The final slice returns the graph's ordered roots, including repeats. -/
def Accepted.revert (a : Accepted g carried) : Stmt P true params results :=
  .seq a.startCode.enableWhile
    (.seq (.while rfl a.test a.body.enableWhile) a.finishCode.enableWhile)

structure Accepted.Laws (a : Accepted g carried) (m : Interpretation.{u,v,w} P) : Prop where
  zero : m.run a.descriptor.zero .nil = some ⟨0⟩
  tick : ∀ k : Nat, m.run a.descriptor.tick (.cons ⟨k⟩ .nil) = some ⟨k + 1⟩
  negate : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩

def Accepted.runFrom (a : Accepted g carried) (m : Interpretation.{u,v,w} P) :
    Nat → Tuple m.Value a.storeTypes → Option (Tuple m.Value results)
  | fuel, store =>
    match a.test.eval m store with
    | none => none
    | some flag =>
      if flag.down then
        match fuel with
        | 0 => none
        | k + 1 => (a.body.runLoopFree m store).bind (a.runFrom m k)
      else a.finishCode.runLoopFree m store
termination_by structural fuel _ => fuel

def Accepted.runFuel (a : Accepted g carried) (m : Interpretation.{u,v,w} P)
    (fuel : Nat) (input : Tuple m.Value params) : Option (Tuple m.Value results) :=
  (a.startCode.runLoopFree m input).bind (a.runFrom m fuel)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed
