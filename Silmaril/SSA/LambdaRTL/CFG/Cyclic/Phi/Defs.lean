module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs

/-! # Predecessor-indexed φ nodes for cyclic λRTL

Each row defines one destination and lists its operands in entry-then-table
predecessor order. Each source has at most one edge to any given target.
Internal branches get their arguments from the target's rows. The distinguished
`none` label is an explicit return and carries its result unchanged.

The source executes with a store and reads every φ operand from the predecessor's
store before installing any destinations. Lowering transposes the rows into
packets and uses cyclic versioning to preserve the other live registers.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- An incoming operand is keyed by `none` for the entry or `some label` for a named block. -/
structure Row (V K : Type w) where
  dst : V
  incoming : List (Option K × Val V)

/-- Named blocks carry their φ rows followed by ordinary λRTL instructions. -/
structure Block (V K : Type w) (F : Type v) where
  rows : List (Row V K)
  body : Body V (Option K) F

/-- The unnamed entry has no φ rows. -/
structure Graph (V K : Type w) (F : Type v) where
  entry : Body V (Option K) F
  blocks : List (K × Block V K F)

/-- An internal jump. Its nominal payload is unused. -/
def br (target : K) : Term V (Option K) F := .br (some target) .unit

/-- The graph's single return exit. -/
def ret (value : Val V) : Term V (Option K) F := .br none value

variable [DecidableEq K]

/-- Predecessors in canonical order. Returns do not contribute an edge. -/
def Graph.predecessors (graph : Graph V K F) (target : K) : List (Option K) :=
  (if some target ∈ graph.entry.targets then [none] else []) ++
    graph.blocks.filterMap fun (label, block) =>
      if some target ∈ block.body.targets then some (some label) else none

variable [DecidableEq V]

/-- Check unique block labels, resolved targets, one edge per (source, target),
and unique destinations within each block. Equality of the predecessor lists
checks the keys, order, and length of every row, including at zero-predecessor
blocks. Each accepted edge therefore has one argument per destination, in row order. -/
def Graph.check (graph : Graph V K F) : Bool :=
  let labels := graph.blocks.map Prod.fst
  let validTargets := fun body : Body V (Option K) F =>
    let targets := body.targets.filterMap id
    decide targets.Nodup && targets.all (fun target => labels.contains target)
  decide labels.Nodup && validTargets graph.entry &&
    graph.blocks.all fun (label, block) =>
      validTargets block.body && decide (block.rows.map Row.dst).Nodup &&
        block.rows.all fun row => decide (row.incoming.map Prod.fst = graph.predecessors label)

/-- The unit default totalizes lookup for hypothetical transfers from non-predecessors.
Every incoming key used by execution of a checked graph is present. -/
def Row.operand (source : Option K) (row : Row V K) : Val V :=
  (row.incoming.lookup source).getD .unit

/-- Transpose one predecessor column into the argument vector, in destination row order. -/
def arguments (source : Option K) (rows : List (Row V K)) : List (Val V) :=
  rows.map (Row.operand source)

/-- Evaluate every RHS in the fixed snapshot and install the results in the destination
store. In ordinary φ execution, both stores start as the predecessor's outgoing store. -/
def assign (model : Model F M α) (source : Option K) (snapshot : V → α) :
    List (Row V K) → (V → α) → (V → α)
  | [], store => store
  | row :: rows, store =>
      assign model source snapshot rows (upd store row.dst ((row.operand source).eval model snapshot))

/-- A completed return or an internal jump carrying its predecessor key. -/
inductive Control (K α : Type w) where
  | returned (value : α)
  | jump (source : Option K) (target : K)

abbrev Pending (V K α : Type w) := Control K α × (V → α)

variable [Monad M]

/-- Execute the original instructions to their next transfer, keeping the outgoing store. -/
def execute (model : Model F M α) (source : Option K) (body : Body V (Option K) F)
    (store : V → α) : M (Pending V K α) :=
  body.exec model (fun target value next =>
    pure (target.elim (.returned value) (.jump source), next)) store

/-- Resolve a predecessor-indexed jump and install its simultaneous φ assignments
before running the target body. An unresolved label is observable as a named exit
on unchecked input. Checked graphs only reach the explicit return exit. -/
def step (model : Model F M α) (graph : Graph V K F) (pending : Pending V K α) :
    M ((Option K × α) ⊕ Pending V K α) :=
  match pending.1 with
  | .returned value => pure (.inl (none, value))
  | .jump source target =>
      match graph.blocks.lookup target with
      | none => pure (.inl (some target, model.unit))
      | some block =>
          Sum.inr <$> execute model (some target) block.body
            (assign model source pending.2 block.rows pending.2)

/-- Complete-Elgot return semantics for the original predecessor-indexed graph. -/
def run [Iterate M] (model : Model F M α) (graph : Graph V K F) (input : V → α) :
    M (Option K × α) :=
  execute model none graph.entry input >>= iter (step model graph)

section Lowering

/-- Embed source variables, reserving `none` for the incoming packet and its tails. -/
def liftVal : Val V → Val (Option V)
  | .var x => .var (some x)
  | .unit => .unit
  | .pair a b => .pair (liftVal a) (liftVal b)

def liftOp : Op V F → Op (Option V) F
  | .val a => .val (liftVal a)
  | .app f a => .app f (liftVal a)
  | .inl a => .inl (liftVal a)
  | .inr a => .inr (liftVal a)
  | .abort a => .abort (liftVal a)

/-- Right-nested product of an edge's arguments. -/
def pack : List (Val V) → Val (Option V)
  | [] => .unit
  | arg :: args => .pair (liftVal arg) (pack args)

/-- Read the selected column on an edge. Unresolved targets occur only on unchecked input. -/
def edgePacket (graph : Graph V K F) (source : Option K) (target : K) : Val (Option V) :=
  pack ((graph.blocks.lookup target).elim [] (fun block => arguments source block.rows))

/-- Lift ordinary bodies, choosing the written argument of each branch. -/
def liftTerm (branchValue : Option K → Val V → Val (Option V)) :
    Term V (Option K) F → Term (Option V) (Option K) F
  | .br target value => .br target (branchValue target value)
  | .case o x left y right =>
      .case (liftOp o) (some x) (liftTerm branchValue left) (some y) (liftTerm branchValue right)

def liftBody (branchValue : Option K → Val V → Val (Option V)) :
    Body V (Option K) F → Body (Option V) (Option K) F
  | .let1 x o body => .let1 (some x) (liftOp o) (liftBody branchValue body)
  | .let2 x y o body => .let2 (some x) (some y) (liftOp o) (liftBody branchValue body)
  | .term term => .term (liftTerm branchValue term)

def lowerTerm (graph : Graph V K F) (source : Option K) :
    Term V (Option K) F → Term (Option V) (Option K) F :=
  liftTerm (fun target value => target.elim (liftVal value) (edgePacket graph source))

def lowerBody (graph : Graph V K F) (source : Option K) :
    Body V (Option K) F → Body (Option V) (Option K) F :=
  liftBody (fun target value => target.elim (liftVal value) (edgePacket graph source))

/-- Decode the already evaluated vector using λRTL's actual pair elimination. -/
def decode (rows : List (Row V K)) (body : Body (Option V) (Option K) F) :
    Body (Option V) (Option K) F :=
  match rows with
  | [] => body
  | row :: rows => .let2 (some row.dst) none (.val (.var none)) (decode rows body)

/-- Use the private parameter to receive and unpack the selected φ arguments. -/
def lowerBlock (graph : Graph V K F) (label : K) (block : Block V K F) :
    CFG.Block (Option V) (Option K) F :=
  ⟨none, decode block.rows (lowerBody graph (some label) block.body)⟩

/-- The tuple-argument CFG before cyclic versioning adds the ordinary live-ins. -/
def lower (graph : Graph V K F) : CFG (Option V) (Option K) F :=
  ⟨lowerBody graph none graph.entry, graph.blocks.map fun (label, block) =>
    (some label, lowerBlock graph label block)⟩

/-- Checked transpose to an executable cyclic lexical CFG. -/
def compile (graph : Graph V K F) : Option (CFG (Option V × Nat) (Option K) F) :=
  if graph.check then some (Versioning.compile (lower graph)) else none

/-- Extend a store with the private packet register. -/
def liftStore (packet : α) (store : V → α) : Option V → α :=
  fun name => name.elim packet store

/-- The lexical evaluator reads source inputs at version zero and uses unit for
the private packet register. Other versions of a free name are immaterial. -/
def inputEnv (model : Model F M α) (input : V → α) : Option V × Nat → α :=
  fun name => liftStore model.unit input name.1

/-- Relate a source transfer to the mutable tuple-argument transfer. -/
def lowerPending (model : Model F M α) (graph : Graph V K F) (pending : Pending V K α) :
    Transfer (Option V) (Option K) α :=
  let store := liftStore model.unit pending.2
  match pending.1 with
  | .returned value => (none, value, store)
  | .jump source target => (some target, (edgePacket graph source target).eval model store, store)

/-- Relate a source transfer to the packet read by the actual cyclic lexical evaluator. -/
def encode (model : Model F M α) (graph : Graph V K F) (pending : Pending V K α) :
    Option K × α :=
  Versioning.encode model (lower graph) (lowerPending model graph pending)

end Lowering

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
