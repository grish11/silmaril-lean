module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Admission.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Defs

/-! # Infer numbered reverse registers for ordered φ splits -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Register Registers Lowered numberedInterface lowerBody)

universe u v

namespace Relocation

/-- The depth of a new local binder and its required physical register. -/
abbrev Demand := Nat × Register.{u}

inductive Origin where
  | input (slot : Nat)
  | parameter
  | local (depth : Nat)

/-- Interpret symbolic binders at the actual numbered allocation. -/
def Origin.register (allocation : Registers Register.{u}) : Origin → Register.{u}
  | .input slot => ⟨slot⟩
  | .parameter => allocation.parameter
  | .local depth => allocation.localAt depth

/-- Replace symbolic origins by registers in the ordered exit record. -/
def renameValue (allocation : Registers Register.{u}) : Val Origin → Val Register.{u}
  | .var origin => .var (origin.register allocation)
  | .unit => .unit
  | .pair left right => .pair (renameValue allocation left) (renameValue allocation right)

/-- Decode the adapter's ordered record of direct register reads. A read of a
fixed input or the packet parameter must already have the requested name. -/
def readDemands (parameter : Register.{u}) :
    Val Origin → List Register.{u} → Option (List Demand.{u})
  | .unit, [] => some []
  | .pair (.var place) tail, wanted :: rest => do
    let more ← readDemands parameter tail rest
    match place with
    | .input slot => if wanted = ⟨slot⟩ then some more else none
    | .parameter => if wanted = parameter then some more else none
    | .local depth => some ((depth, wanted) :: more)
  | _, _ => none

def termDemands {F : Type v} {b e : Nat} (parameter : Register.{u})
    (fields : Fin e → List Register.{u}) :
    CFG.Term Origin (Fin (b + e)) F → Option (List Demand.{u})
  | .br label value =>
    SSA.FiniteSum.append (fun _ : Fin b => some []) (fun i =>
      match value with
      | .pair _ liveOut => readDemands parameter liveOut (fields i)
      | _ => none) label
  | .case _ _ left _ right => do
    let l ← termDemands parameter fields left
    let r ← termDemands parameter fields right
    return l ++ r

def bodyDemands {F : Type v} {b e : Nat} (parameter : Register.{u})
    (fields : Fin e → List Register.{u}) :
    CFG.Body Origin (Fin (b + e)) F → Option (List Demand.{u})
  | .term tail => termDemands parameter fields tail
  | .let1 _ _ body | .let2 _ _ _ body => bodyDemands parameter fields body

/-- Keep body boundaries so conflicts between individually satisfiable
bodies can be distinguished from conflicts inside a body. -/
structure DemandTable where
  entry : List Demand.{u}
  blocks : List (List Demand.{u})

def DemandTable.all (table : DemandTable.{u}) : List Demand.{u} :=
  table.entry ++ table.blocks.flatten

/-- Use the reverse body's binder order with symbolic names. Keeping all
branch arguments in this pass exposes the original ordered live-out reads. -/
def tableDemands {F : Type v} {b e n : Nat} (parameter : Register.{u})
    (fields : Fin e → List Register.{u}) (code : FiniteCFG F b e n) :
    Option DemandTable.{u} := do
  let symbolic : Registers Origin := ⟨.parameter, .local⟩
  let scan := fun {depth : Nat} (names : Fin depth → Option Origin) (body : Flat F (b + e) depth) =>
    (lowerBody symbolic id (fun _ => true) names 0 body).bind (bodyDemands parameter fields)
  let entry ← scan (fun i => some (.input i.val)) code.entry
  let rows ← (List.finRange b).mapM fun i =>
    scan (Fin.cases (some Origin.parameter) (fun _ => none)) (code.block i)
  return ⟨entry, rows⟩

def demands {F : Type v} {b e n : Nat} (parameter : Register.{u})
    (fields : Fin e → List Register.{u}) (code : FiniteCFG F b e n) :
    Option (List Demand.{u}) :=
  (tableDemands parameter fields code).map DemandTable.all

def termBinders {K : Type (u + 1)} {F : Type v} :
    CFG.Term Register.{u} K F → List Register.{u}
  | .br .. => []
  | .case _ x left y right => x :: y :: (termBinders left ++ termBinders right)

def bodyBinders {K : Type (u + 1)} {F : Type v} :
    CFG.Body Register.{u} K F → List Register.{u}
  | .term tail => termBinders tail
  | .let1 x _ body => x :: bodyBinders body
  | .let2 x y _ body => x :: y :: bodyBinders body

/-- Reserve registers used by the original emitted allocation. -/
def writtenRegisters {K : Type (u + 1)} {F : Type v}
    (graph : CFG Register.{u} K F) : List Register.{u} :=
  bodyBinders graph.entry ++ graph.blocks.flatMap fun item => item.2.param :: bodyBinders item.2.body

def firstSpare (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Demand.{u}) : Nat :=
  ((previous.map ULift.down ++ needed.map (fun pair => pair.2.down)).foldr max
    (max captures parameter.down)) + 1

/-- Preserve demanded physical names and assign all other depths in a
disjoint range above the original reverse output and the demanded names. -/
def complete (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Demand.{u}) : Registers Register.{u} :=
  ⟨parameter, fun depth => (needed.lookup depth).getD
    ⟨firstSpare captures parameter previous needed + depth⟩⟩

/-- The same depth must meet all requests in all bodies. A register may be
reused across bodies at that depth, with a single global depth allocation. -/
def satisfies (allocation : Registers Register.{u}) (needed : List Demand.{u}) : Bool :=
  needed.all fun (depth, name) => decide (allocation.localAt depth = name)

/-- Freshness of forced locals and injectivity of their depth-to-register map.
The independent request check also detects two names demanded at one depth. -/
def compatible (captures : Nat) (parameter : Register.{u}) (needed : List Demand.{u}) : Bool :=
  decide (captures ≤ parameter.down) &&
    needed.all (fun (_, name) => decide (captures ≤ name.down ∧ name ≠ parameter)) &&
    needed.all fun first => needed.all fun second =>
      decide (first.2 = second.2 → first.1 = second.1)

/-- The finite requests form a partial bijection between binder depths and
local registers. The parameter and all requested registers are outside the
numbered captures, and requested locals are distinct from the parameter. -/
structure Constraints (captures : Nat) (parameter : Register.{u}) (needed : List Demand.{u}) : Prop where
  parameterOutside : captures ≤ parameter.down
  localsOutside : ∀ request ∈ needed, captures ≤ request.2.down ∧ request.2 ≠ parameter
  oneNamePerDepth : ∀ a ∈ needed, ∀ b ∈ needed, a.1 = b.1 → a.2 = b.2
  oneDepthPerName : ∀ a ∈ needed, ∀ b ∈ needed, a.2 = b.2 → a.1 = b.1

/-- A global numbered allocation satisfying these ordered exit reads. -/
structure Valid (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Demand.{u}) (allocation : Registers Register.{u}) : Prop where
  sameParameter : allocation.parameter = parameter
  parameterOutside : captures ≤ allocation.parameter.down
  distinctLocals : Function.Injective allocation.localAt
  localsOutside : ∀ depth, captures ≤ (allocation.localAt depth).down ∧
    allocation.localAt depth ≠ allocation.parameter
  reads : ∀ request ∈ needed, allocation.localAt request.1 = request.2
  unrequestedFresh : ∀ depth, needed.lookup depth = none →
    ∀ name ∈ previous, allocation.localAt depth ≠ name

/-- Solve the finite constraints before running actual reverse readback. -/
def infer (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Demand.{u}) : Option (Registers Register.{u}) :=
  let candidate := complete captures parameter previous needed
  if compatible captures parameter needed && satisfies candidate needed then some candidate else none

end Relocation

variable {κ V W K : Type (u + 1)} {n : Nat}
  [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} [DecidableEq P.Instr]
  {context : BoundCtx (Ty κ) n} {exits : List (Option K)} {external : Fin exits.length → Ty κ}
  {fields : Option K → List (Register × Ty κ)} {C : Captures V context} {plan : Plan V W K K}

local notation "Ports" => numberedInterface context exits external
variable {a : Admission P (numberedInterface context exits external) fields C}

/-- A checked original reverse allocation and its actual output. -/
structure ReverseSeed (a : Admission P (numberedInterface context exits external) fields C) where
  registers : Registers Register
  labels : Fin (Versioning.compile (Phi.OrderedExits.lower a.source)).blocks.length → Option K
  output : Lowered Ports fields a.code
  accepted : a.reverseChecked registers labels = some output

/-- Collect requests at the actual generated table using the ordered exit
fields of the original reverse interface. -/
def GeneratedSplit.relocationDemands (split : GeneratedSplit plan a) (seed : ReverseSeed a) :
    Option (List Relocation.Demand.{u}) :=
  Relocation.demands seed.registers.parameter (fun i => (fields exits[i]).map Prod.fst) split.target.code

/-- Infer physical registers for the generated split. The original output
reserves the old local names, and the original packet parameter is kept. -/
def GeneratedSplit.relocatedRegisters (split : GeneratedSplit plan a) (seed : ReverseSeed a) :
    Option (Registers Register) :=
  (split.relocationDemands seed).bind (Relocation.infer n seed.registers.parameter
    (Relocation.writtenRegisters seed.output.source))

/-- Infer the allocation and run the existing exact reverse checker. -/
def GeneratedSplit.reverseRelocated (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K) :
    Option (Lowered Ports fields split.target.code) :=
  (split.relocatedRegisters seed).bind fun registers => split.target.reverseChecked registers labels

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
