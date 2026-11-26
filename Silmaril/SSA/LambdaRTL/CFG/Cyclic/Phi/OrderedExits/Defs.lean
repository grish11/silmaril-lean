module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed.Defs

/-! # Explicit external labels for predecessor-indexed φ graphs -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq K]

/-- The block table determines internal destinations. The ordered admission
also checks that every other used destination is a declared exit. -/
def lookup (graph : Graph V K F) (target : Option K) : Option (Block V K F) :=
  target.bind fun key => graph.blocks.lookup key

/-- For scope analysis, identify the declared exits with the old return.
This keeps their payload reads and leaves the internal φ rows intact. -/
def forScope (graph : Graph V K F) (exits : List (Option K)) : Graph V K F :=
  let label := fun target => if exits.contains target then none else target
  ⟨graph.entry.relabel label, graph.blocks.map fun (key, block) =>
    (key, ⟨block.rows, block.body.relabel label⟩)⟩

/-- Distinct external labels may not name blocks. Every written branch names
either a block or one of the supplied exits. The existing φ checker
validates normalized predecessor rows, definitions, and arrival claims. -/
def check [DecidableEq V] (graph : Graph V K F) (exits : List (Option K))
    (inputs : List V) (certificate : GlobalSSA.Certificate V K) : Bool :=
  let targets := graph.entry.targets ++ graph.blocks.flatMap (fun item => item.2.body.targets)
  decide exits.Nodup && exits.all (fun exit => (lookup graph exit).isNone) &&
    targets.all (fun target => (lookup graph target).isSome || exits.contains target) &&
    GlobalSSA.check (forScope graph exits) inputs certificate

/-- Keep the predecessor, written destination and payload, and outgoing store. -/
abbrev Pending (V K α : Type w) := Option K × Transfer V (Option K) α

variable [DecidableEq V] [Monad M]

def execute (model : Model F M α) (pred : Option K) (body : Body V (Option K) F)
    (store : V → α) : M (Pending V K α) :=
  body.exec model (fun target value next => pure (pred, target, value, next)) store

/-- An internal hit installs φ values from the predecessor snapshot. On an
external exit the source returns the written label and payload. -/
def step (model : Model F M α) (graph : Graph V K F) (pending : Pending V K α) :
    M ((Option K × α) ⊕ Pending V K α) :=
  let (pred, target, value, store) := pending
  match lookup graph target with
  | none => pure (.inl (target, value))
  | some block =>
    Sum.inr <$> execute model target block.body (assign model pred store block.rows store)

def run [Iterate M] (model : Model F M α) (graph : Graph V K F) (input : V → α) :
    M (Option K × α) :=
  execute model none graph.entry input >>= iter (step model graph)

/-- Preserve exit arguments and transpose only the internal φ edges. -/
def branchValue (graph : Graph V K F) (pred target : Option K) (value : Val V) : Val (Option V) :=
  (lookup graph target).elim (liftVal value) (fun block => pack (arguments pred block.rows))

def lowerBlock (graph : Graph V K F) (key : K) (block : Block V K F) :
    CFG.Block (Option V) (Option K) F :=
  ⟨none, decode block.rows (liftBody (branchValue graph (some key)) block.body)⟩

def lower (graph : Graph V K F) : CFG (Option V) (Option K) F :=
  ⟨liftBody (branchValue graph none) graph.entry, graph.blocks.map fun (key, block) =>
    (some key, lowerBlock graph key block)⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits
