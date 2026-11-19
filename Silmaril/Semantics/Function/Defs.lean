module

public import Silmaril.Semantics.Region.Abstract.Defs
public import Silmaril.Semantics.Graph.Defs

/-! # Raw function and call judgments

The context qualifies all evidence (for example, an image and an interface).
Bodies are opaque rows, not a partition or a coverage claim. An internal
identity is not a symbol name unless the client chooses it to be one.
-/

@[expose] public section
namespace Silmaril.Semantics.Function
universe u

structure Signature where
  Context : Type u
  Internal : Type u
  Foreign : Type u
  Site : Type u
  Body : Type u

inductive Node (sig : Signature.{u}) where
  | localFn (name : sig.Internal)
  | foreign (name : sig.Foreign)

inductive Transfer where
  | invoke
  | tail
  deriving DecidableEq, Repr

inductive Dispatch where
  | direct
  | indirect
  deriving DecidableEq, Repr

structure CallSite (sig : Signature.{u}) where
  caller : sig.Internal
  site : sig.Site
  transfer : Transfer

structure Edge (sig : Signature.{u}) where
  origin : CallSite sig
  dispatch : Dispatch
  callee : Node sig

inductive Atom (sig : Signature.{u}) where
  | node (context : sig.Context) (name : Node sig)
  | body (context : sig.Context) (name : sig.Internal) (row : sig.Body)
  | call (context : sig.Context) (edge : Edge sig)

abbrev Model (sig : Signature.{u}) := Region.Abstract.RawModel (Atom sig)
abbrev Decomposition (sig : Signature.{u}) := sig.Internal → sig.Body → Prop
abbrev Calls (sig : Signature.{u}) := Edge sig → Prop

/-- Independent coverage and overlap policies for clients that want a cover
or a partition. Multiple rows per owner remain possible. -/
def Decomposition.Covers {sig : Signature.{u}} {Label : Type u} (rows : Decomposition sig)
    (support : sig.Body → Set Label) (required : Set Label) : Prop :=
  ∀ label ∈ required, ∃ name row, rows name row ∧ label ∈ support row

def Decomposition.UniqueOwner {sig : Signature.{u}} {Label : Type u} (rows : Decomposition sig)
    (support : sig.Body → Set Label) : Prop :=
  ∀ lhs rhs first second label, rows lhs first → rows rhs second →
    label ∈ support first → label ∈ support second → lhs = rhs

def decomposition {sig : Signature.{u}} (model : Model sig) (context : sig.Context) :
    Decomposition sig := fun name row => Atom.body context name row ∈ model

def calls {sig : Signature.{u}} (model : Model sig) (context : sig.Context) : Calls sig :=
  fun edge => Atom.call context edge ∈ model

def bundle {sig : Signature.{u}} (bodies : sig.Context → Decomposition sig)
    (edges : sig.Context → Calls sig) (present : sig.Context → Node sig → Prop) : Model sig :=
  {atom | match atom with
    | .body context name row => bodies context name row
    | .call context edge => edges context edge
    | .node context name => present context name}

/-- Presence is positive. Uniqueness, disjointness, completeness and semantic
validity are intentionally outside this closure system. -/
inductive PresenceRule {sig : Signature.{u}} : Region.Abstract.Rule (Atom sig) → Prop where
  | body (context : sig.Context) (name : sig.Internal) (row : sig.Body) :
      PresenceRule ⟨{.body context name row}, .node context (.localFn name)⟩
  | caller (context : sig.Context) (edge : Edge sig) :
      PresenceRule ⟨{.call context edge}, .node context (.localFn edge.origin.caller)⟩
  | callee (context : sig.Context) (edge : Edge sig) :
      PresenceRule ⟨{.call context edge}, .node context edge.callee⟩

abbrev Laws (sig : Signature.{u}) : Region.Abstract.Rules (Atom sig) := {rule | PresenceRule rule}
abbrev LawfulModel (sig : Signature.{u}) := Region.Abstract.ClosedModel (Laws sig)

/-- `none` is Top, not an empty set. `some ∅` is a genuine empty upper bound. -/
def admits {α : Type u} (bound : Option (Set α)) (target : α) : Prop :=
  match bound with
  | none => True
  | some targets => target ∈ targets

def MayCover {sig : Signature.{u}} (actual possible : Calls sig) : Prop :=
  ∀ ⦃edge⦄, actual edge → possible edge

/-- Partial results can contain known edges and unresolved sites at once.
Absence from `indirect` does not certify absence of uninspected transfers. -/
structure Analysis (sig : Signature.{u}) where
  direct : CallSite sig → Node sig → Prop
  indirect : CallSite sig → Option (Set (Node sig)) → Prop

def Analysis.may {sig : Signature.{u}} (analysis : Analysis sig) : Calls sig := fun edge =>
  match edge.dispatch with
  | .direct => analysis.direct edge.origin edge.callee
  | .indirect => ∃ bound, analysis.indirect edge.origin bound ∧ admits bound edge.callee

def Analysis.DirectOnly {sig : Signature.{u}} (analysis : Analysis sig) : Prop :=
  ∀ origin bound, ¬ analysis.indirect origin bound

/-- Weaken the bounds of known indirect sites only. This does not certify the
site inventory or generate an indirect site where no evidence was recorded. -/
def Analysis.topify {sig : Signature.{u}} (analysis : Analysis sig) : Analysis sig where
  direct := analysis.direct
  indirect site bound := bound = none ∧ ∃ old, analysis.indirect site old

def graph {sig : Signature.{u}} (edges : Calls sig) (accept : Dispatch → Prop) :
    Graph.RelGraph (Node sig) :=
  ⟨fun source dest => ∃ edge, edges edge ∧ accept edge.dispatch ∧
    source = .localFn edge.origin.caller ∧ dest = edge.callee⟩

def mayGraph {sig : Signature.{u}} (edges : Calls sig) := graph edges (fun _ => True)
def directGraph {sig : Signature.{u}} (edges : Calls sig) := graph edges (· = .direct)

abbrev Reachable {sig : Signature.{u}} (g : Graph.RelGraph (Node sig)) := Relation.ReflTransGen g.edge
abbrev CallPath {sig : Signature.{u}} (g : Graph.RelGraph (Node sig)) := Relation.TransGen g.edge

def foreignFrontier {sig : Signature.{u}} (g : Graph.RelGraph (Node sig))
    (entry : sig.Internal) : Set sig.Foreign :=
  {leaf | CallPath g (.localFn entry) (.foreign leaf)}

def reachableCalls {sig : Signature.{u}} (edges : Calls sig) (accept : Dispatch → Prop)
    (entry : sig.Internal) : Set (Edge sig) :=
  {edge | edges edge ∧ accept edge.dispatch ∧
    Reachable (graph edges accept) (.localFn entry) (.localFn edge.origin.caller)}

/-- A reported set is exact with both a closure invariant and witnesses. -/
structure ReachCertificate {α : Type u} (g : Graph.RelGraph α) (root : α) (seen : Set α) : Prop where
  root_mem : root ∈ seen
  step_closed : ∀ ⦃source dest⦄, source ∈ seen → g.edge source dest → dest ∈ seen
  witnessed : ∀ ⦃dest⦄, dest ∈ seen → Relation.ReflTransGen g.edge root dest

def DecomposeProblem {sig : Signature.{u}} (accept : Decomposition sig → Prop)
    (context : sig.Context) (answer : Model sig) : Prop := accept (decomposition answer context)

def CallGraphProblem {sig : Signature.{u}} (actual : Calls sig) (answer : Analysis sig) : Prop :=
  MayCover actual answer.may

def ReachProblem {sig : Signature.{u}} (g : Graph.RelGraph (Node sig))
    (root : Node sig) (answer : Set (Node sig)) : Prop :=
  ∀ dest, dest ∈ answer ↔ Reachable g root dest

def PathProblem {sig : Signature.{u}} (g : Graph.RelGraph (Node sig))
    (root : Node sig) (answer : Set (Node sig)) : Prop :=
  ∀ dest, dest ∈ answer ↔ CallPath g root dest

def ReachableCallsProblem {sig : Signature.{u}} (edges : Calls sig) (accept : Dispatch → Prop)
    (entry : sig.Internal) (answer : Set (Edge sig)) : Prop := answer = reachableCalls edges accept entry

def FrontierProblem {sig : Signature.{u}} (g : Graph.RelGraph (Node sig))
    (entry : sig.Internal) (answer : Set sig.Foreign) : Prop := answer = foreignFrontier g entry

end Silmaril.Semantics.Function
