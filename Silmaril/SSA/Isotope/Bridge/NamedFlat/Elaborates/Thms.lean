module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Elaborates.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Elaborates

/-! # When the named elaboration succeeds

The versioning and the elaboration of a named graph succeed at given
captures under three checks on the source: its operands are in the
fragment, its jumps go to blocks or declared exits, and its versioned
entry reads only captures at their initial version. No success of the
elaboration is assumed.

There is no condition on the blocks. The versioning carries on every edge
a record of every register that some body reads, without the parameter of
the target, and the target unpacks all of it before it runs. So a
versioned block reads only its own parameter, whatever the graph is, and
its body elaborates under the name of that parameter alone. Only the
entry reads registers that nothing binds, and those have to be captures.

For a φ graph the three checks follow from checks on the φ graph. The
lowering keeps the fragment and the labels. When the existing check
accepts the graph with every block arriving with the given registers
only, the versioned entry reads those registers only, at their initial
version. So the lowering elaborates at any captures that cover them. For
the normalized graph of a closed forwarding table, the registers are the
declared inputs; and a ranked graph with claims that list no register of
their block has a closed inferred table. The captures are exactly the
ones given, and the exits are the declared ones in their order.

This is success of the untyped elaboration. The typed elaboration
`compileTyped` runs it and then checks the result against a capture
context, a type for the packet of every block, and the types of the
exits. That check, `check target β R L = true`, is the one typed
hypothesis that remains: given it, `compileTyped` returns the same
graph with its typing. Nothing here derives it from types on the φ graph.
A packet type has to give a type to the φ operands of the block and to
every register in the record.
-/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic

universe u v w

section Named

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K] {n : Nat}

/-- A versioned block reads only its parameter freely. -/
theorem compileBlock_names (graph : CFG V K F) (item : K × CFG.Block V K F)
    (member : item ∈ graph.blocks) :
    ∀ name ∈ (Versioning.compileBlock graph item.2).body.toRegion.fvList,
      name = (item.2.param, 0) :=
  compileBlock_names_proof graph item member

/-- The versioning and the elaboration of a named graph succeed at the
given captures, when its operands are in the fragment, its jumps go to
blocks or declared exits, and the versioned entry reads only captures at
their initial version. -/
theorem compile_isSome (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    (fragment : plain source = true) (known : resolves source exits = true)
    (named : entryNamed source captures = true) :
    (compile source exits captures).isSome = true :=
  compile_isSome_proof source exits captures fragment known named

end Named

section Typed

variable {V K : Type u} {F : Type v} [DecidableEq V] [DecidableEq K] {n : Nat}
  {Base : Type u} [DecidableEq Base] [HasTy F (Ty Base)]

/-- The typed elaboration succeeds, with the elaborated graph, when the
elaboration succeeds and its result passes the typing check. -/
theorem compileTyped_of_check (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    (captureTypes : BoundCtx (Ty Base) n)
    (internal : Fin (Versioning.compile source).blocks.length → Ty Base)
    (external : Fin exits.length → Ty Base)
    {target : LambdaSSA.FiniteCFG F (Versioning.compile source).blocks.length exits.length n}
    (elaborated : compile source exits captures = some target)
    (typed : check target captureTypes internal external = true) :
    ∃ result, compileTyped source exits captures captureTypes internal external = some result ∧
      result.val = target := by
  unfold compileTyped
  generalize compile source exits captures = found at elaborated ⊢
  subst elaborated
  exact ⟨⟨target, rfl, check_sound target captureTypes internal external typed⟩,
    by simp only [typed, ↓reduceDIte], rfl⟩

end Typed

namespace Phi

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph OrderedExits.lower OrderedExits.checkExits
  OrderedExits.check Forward.Name Forward.Table Forward.forward Forward.closed Forward.entryKept
  Forward.infer Forward.claimed Forward.ranked)

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K] {n : Nat}

omit [DecidableEq V] in
/-- The lowering of a φ graph in the fragment is in the fragment. -/
theorem lower_plain (graph : Graph V K F) (fragment : plain graph = true) :
    NamedFlat.plain (OrderedExits.lower graph) = true :=
  lower_plain_proof graph fragment

omit [DecidableEq V] in
/-- The jumps of the lowering of a φ graph go to blocks or declared exits,
when no declared exit is a block and every jump of the φ graph goes to a
block or a declared exit. -/
theorem lower_resolves (graph : Graph V K F) (exits : List (Option K))
    (partition : OrderedExits.checkExits graph exits = true) :
    resolves (OrderedExits.lower graph) exits = true :=
  lower_resolves_proof graph exits partition

/-- The lowering of a φ graph elaborates at captures that cover the given
registers, when the existing check accepts the graph with every block
arriving with those registers only and its operands are in the
fragment. -/
theorem compile_isSome (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (captures : Fin n → Option V)
    (ok : OrderedExits.check graph exits inputs
      (graph.blocks.map fun (key, _) => (key, inputs)) = true)
    (fragment : plain graph = true) (covered : ∀ z ∈ inputs, ∃ i, captures i = some z) :
    (compile (OrderedExits.lower graph) exits captures).isSome = true :=
  checked_compile_proof graph exits inputs captures ok fragment covered

/-- The normalized graph of a φ graph in the fragment is in the
fragment. -/
theorem forward_plain (graph : Graph V K F) (table : Forward.Table V K)
    (fragment : plain graph = true) : plain (Forward.forward graph table) = true :=
  forward_plain_proof graph table fragment

/-- The lowering of the normalized graph of a closed table elaborates at
captures that cover the declared inputs. -/
theorem compile_of_closed (graph : Graph V K F) (table : Forward.Table V K)
    (exits : List (Option K)) (inputs : List V) (captures : Fin n → Option (Forward.Name V K))
    (isClosed : Forward.closed graph table exits inputs = true) (fragment : plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z)) :
    (compile (OrderedExits.lower (Forward.forward graph table)) exits captures).isSome = true :=
  closed_compile_proof graph table exits inputs captures isClosed fragment covered

/-- The same for a table that keeps the entry, closed or not. -/
theorem compile_of_entryKept (graph : Graph V K F) (table : Forward.Table V K)
    (exits : List (Option K)) (inputs : List V) (captures : Fin n → Option (Forward.Name V K))
    (partition : OrderedExits.checkExits graph exits = true)
    (kept : Forward.entryKept graph table inputs = true) (fragment : plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z)) :
    (compile (OrderedExits.lower (Forward.forward graph table)) exits captures).isSome = true :=
  kept_compile_proof graph table exits inputs captures partition kept fragment covered

/-- For a ranked φ graph in the fragment that the existing check accepts
with claims that list no register of their block, the lowering of the
normalized graph of the inferred table elaborates at captures that cover
the declared inputs. -/
theorem compile_infer_of_ranked (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (certificate : CFG.Cyclic.Phi.GlobalSSA.Certificate V K) (rank : K → Nat)
    (captures : Fin n → Option (Forward.Name V K))
    (ok : OrderedExits.check graph exits inputs certificate = true)
    (claims : Forward.claimed graph certificate = true)
    (acyclic : Forward.ranked graph rank = true) (fragment : plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z)) :
    (compile (OrderedExits.lower (Forward.forward graph (Forward.infer graph exits inputs))) exits
      captures).isSome = true :=
  compile_of_closed graph _ exits inputs captures
    (CFG.Cyclic.Phi.Forward.closed_infer_of_ranked graph exits inputs certificate rank ok claims
      acyclic) fragment covered

end Phi

end Silmaril.Isotope.Bridge.NamedFlat
