module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Correctness
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Mathlib.Data.List.Chain

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Inversion.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta (Term)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending)
open Relation (ReflTransGen)

theorem chain_reaches {M : Type} {step : M → M → Prop} (start : M) (rest : List M)
    (chain : List.IsChain step (start :: rest)) : ReflTransGen step start (rest.getLastD start) := by
  induction rest generalizing start with
  | nil => exact .refl
  | cons next rest ih =>
    obtain ⟨first, later⟩ := List.isChain_cons_cons.mp chain
    rw [List.getLastD_cons]
    exact (ih next later).head first

private theorem first_ready {M : Type} {step : M → M → Prop} (ready : M → Bool)
    (start : M) (rest : List M) (chain : List.IsChain step (start :: rest))
    (atStart : ready start = false) (atEnd : ready (rest.getLastD start) = true) :
    ∃ earlier before after later, start :: rest = earlier ++ before :: after :: later ∧
      (∀ point ∈ earlier, ready point = false) ∧ ready before = false ∧ ready after = true ∧
      step before after ∧ ReflTransGen step start after ∧ ReflTransGen step after (rest.getLastD start) := by
  induction rest generalizing start with
  | nil =>
    rw [List.getLastD_nil, atStart] at atEnd
    cases atEnd
  | cons next rest ih =>
    obtain ⟨fire, remains⟩ := List.isChain_cons_cons.mp chain
    rw [List.getLastD_cons] at atEnd ⊢
    cases encountered : ready next with
    | true =>
      exact ⟨[], start, next, rest, rfl, by simp, atStart, encountered,
        fire, .single fire, chain_reaches next rest remains⟩
    | false =>
      obtain ⟨earlier, before, after, later, split, absent, beforeReady, ready, fired, ran, restRan⟩ :=
        ih next remains encountered atEnd
      refine ⟨start :: earlier, before, after, later, congrArg (List.cons start) split,
        ?_, beforeReady, ready, fired, ran.head fire, restRan⟩
      intro mark mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact atStart
      · exact absent mark mem

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (old : Bank (regs := regs) model)

private theorem outer_initial : readOuter p old (pending semantics (thetaBody p)) = none := by
  change finished semantics (outerRegion p) old PUnit.unit
    ((outerCut p).2.2.observe semantics (pending semantics (thetaBody p))) = none
  rw [(outerCut p).2.2.observe_pending]
  have ofVertices {args results : List (SeaOfNodes.Diamond.Ty Width)}
      {sigs : List (List (SeaOfNodes.Diamond.Ty Width))}
      (term : Term (Join.Opcode Op) args [] sigs results)
      (entry : RVSDG.Tuple semantics.Val args) (vertices : sigs ≠ []) :
      finished semantics term entry PUnit.unit (pending semantics term) = none := by
    cases term with
    | ret => exact False.elim (vertices rfl)
    | bind => rfl
  apply ofVertices
  simp [Nested.Numbered.splitSigs]

/-- Locate the first published outer bank in the actual supplied list.
The returned before/after markings are adjacent in that list. -/
theorem first_outer (rest : List (Marking semantics (thetaBody p)))
    (chain : List.IsChain (Fire semantics (thetaBody p) old PUnit.unit)
      (pending semantics (thetaBody p) :: rest))
    (done : (finished semantics (thetaBody p) old PUnit.unit
      (rest.getLastD (pending semantics (thetaBody p)))).isSome) :
    ∃ earlier before after later,
      pending semantics (thetaBody p) :: rest = earlier ++ before :: after :: later ∧
      (∀ point ∈ earlier, readOuter p old point = none) ∧ readOuter p old before = none ∧
      Fire semantics (thetaBody p) old PUnit.unit before after ∧
      readOuter p old after = some (packetsAt p old).outer.2 ∧
      (outerCut p).2.2.observe semantics after =
        (outerCut p).2.2.observe semantics (rest.getLastD (pending semantics (thetaBody p))) := by
  let ready := fun mark => (readOuter p old mark).isSome
  have completed := body_eq p old (chain_reaches _ _ chain) done
  have endReady : ready (rest.getLastD (pending semantics (thetaBody p))) = true :=
    Option.isSome_iff_exists.mpr ⟨_, completed.1⟩
  obtain ⟨earlier, before, after, later, split, absent, beforeReady, hit, fire, ran, remaining⟩ :=
    first_ready ready _ rest chain (by simp [ready, outer_initial p old]) endReady
  obtain ⟨bank, read⟩ := Option.isSome_iff_exists.mp hit
  refine ⟨earlier, before, after, later, split, ?_, Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp beforeReady), fire,
    read.trans (congrArg some (outer_eq p old ran read)), stable_outer p old read remaining⟩
  intro mark mem
  exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp (absent mark mem))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Inversion.Proofs
