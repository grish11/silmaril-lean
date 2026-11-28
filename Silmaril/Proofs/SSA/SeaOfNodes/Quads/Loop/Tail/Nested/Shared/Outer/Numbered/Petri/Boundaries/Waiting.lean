module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Proofs

open SeaOfNodes.Diamond (Ty ValueSort dataPorts lastIndex lastPort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG (Tuple Port Locals Wires extend)
open RVSDG.Petri (Tokens read collect colour)
open RVSDG.NestedTheta (Term Graph)
open RVSDG.NestedTheta.Petri (Cut Fire Marking finished pending finishes_iff finishes_term_iff)
open Join.Finite (lastBank)
open Shared.MLIR.CF.InnerPhi (headerBank)
open Relation (ReflTransGen)

universe u v w

theorem base_cut_wires {V S : Type u} {Φ : RVSDG.Dialect.{u, v} V S}
    {args bank outs : List (RVSDG.PortType V S)} {past frontSigs tailSigs : List (List (RVSDG.PortType V S))}
    (base : RVSDG.Term Φ args past frontSigs bank)
    (finish : Wires args (extend past frontSigs) bank → Term Φ args (extend past frontSigs) tailSigs outs) :
    (baseCut base finish).wires = endWires base := by
  induction base with
  | ret => rfl
  | bind _ _ _ _ ih => exact ih _

variable {Data : Type u} {F : SeaOfNodes.Diamond.Ty Data → Type w}
variable {args head : List (SeaOfNodes.Diamond.Ty Data)} {past : List (List (SeaOfNodes.Diamond.Ty Data))}

theorem last_colour {t : SeaOfNodes.Diamond.Ty Data} (port : Port head t)
    (tokens : Tokens F past) (values : Tuple F head) :
    ((tokens.snoc (values.map fun _ => some)).get (lastIndex head past)).get (lastPort port past) =
      some (values.get port) := by
  induction past with
  | nil => exact SeaOfNodes.Diamond.LambdaSSA.tuple_get_map _ _ _
  | cons _ _ ih => exact ih tokens.2

private theorem read_last (entry : Tuple F args) (tokens : Tokens F past) (values : Tuple F head) :
    RVSDG.Petri.read (lastBank past head) entry (tokens.snoc (values.map fun _ => some)) = some values := by
  unfold RVSDG.Petri.read
  have allColours :
      (lastBank past head).map (fun _ => colour entry (tokens.snoc (values.map fun _ => some))) =
        values.map (fun _ => some) := by
    refine (tabulate_get_eq _).symm.trans ((congrArg (tabulate head) (funext fun _ => funext fun port => ?_)).trans
      (tabulate_get_eq _))
    rw [SeaOfNodes.Diamond.LambdaSSA.tuple_get_map, SeaOfNodes.Diamond.LambdaSSA.tuple_get_map, lastBank, get_tabulate]
    exact last_colour port tokens values
  rw [allColours]
  clear allColours
  induction values with
  | nil => rfl
  | cons _ _ ih => simp only [Tuple.map, collect, ih]

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (old : Bank (regs := regs) model)

private theorem header_run :
    (Term.ofBase (headerCode p)).toGraph.run semantics 0 old = some (headerBank p.toRoutes old) := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph, Term.run_ofBase]
  unfold RVSDG.Term.run headerCode
  erw [Join.Block.lowerFrom_eval, read_initial]
  rfl

theorem waiting_reaches_with {results : List (SeaOfNodes.Diamond.Ty Width)} {suffix : List (List (SeaOfNodes.Diamond.Ty Width))}
    (finish : Wires (dataPorts regs) (outerScope p) (dataPorts regs) →
      Term (Join.Opcode Op) (dataPorts regs) (outerScope p) suffix results)
    (arm : Fin 2)
    (chosen : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = arm)
    (child : Marking semantics (Prefix.outerArm p.toRoutes arm))
    (childSteps : ReflTransGen (Fire semantics (Prefix.outerArm p.toRoutes arm) (headerBank p.toRoutes old) PUnit.unit)
      (pending semantics (Prefix.outerArm p.toRoutes arm)) child) :
    let after := fun bank => Prefix.afterOuter p.toRoutes bank finish
    let cut := baseCut (headerCode p) after
    ∃ headerMark, ReflTransGen (Fire semantics (Prefix.afterHeader p.toRoutes finish) old PUnit.unit)
      (pending semantics (Prefix.afterHeader p.toRoutes finish))
      (cut.attach semantics headerMark
        (.done (taggedHeader p old arm), .waiting arm (headerBank p.toRoutes old, child),
          pending semantics (finish (lastBank _ _)))) := by
  let front := Term.ofBase (headerCode p)
  let after := fun bank => Prefix.afterOuter p.toRoutes bank finish
  let continuation := after (endWires (headerCode p))
  let cut := baseCut (headerCode p) after
  let header := headerBank p.toRoutes old
  have headerDone := (finishes_iff semantics front.toGraph old header).mpr ⟨0, header_run p old⟩
  obtain ⟨mark, reaches, readHeader⟩ := (finishes_term_iff semantics front old header).mp headerDone
  let tokens := cut.tokens semantics PUnit.unit mark
  have ready : RVSDG.Petri.read (endWires (headerCode p)) old tokens = some header := by
    have parts := cut.read_after semantics old PUnit.unit mark header readHeader
    change RVSDG.Petri.read cut.wires old tokens = some header at parts
    rw [base_cut_wires] at parts
    exact parts
  let routed := taggedHeader p old arm
  let rest := pending semantics (finish (lastBank _ _))
  let markedRoute : Marking semantics continuation := (.done routed, .pending, rest)
  let liveMark (mark : Marking semantics (Prefix.outerArm p.toRoutes arm)) : Marking semantics continuation :=
    (.done routed, .waiting arm (header, mark), rest)
  have firesRoute : Fire semantics continuation old tokens (pending semantics continuation) markedRoute := by
    apply Fire.primitive ready
    have routedEq : taggedHeader p old ((Prefix.outerChoice p.toRoutes).eval header) = routed :=
      congrArg (taggedHeader p old) chosen
    exact congrArg some routedEq
  have entersArm : Fire semantics continuation old tokens markedRoute
      (liveMark (pending semantics (Prefix.outerArm p.toRoutes arm))) :=
    .later (.enter (read_last old tokens routed) rfl)
  have advanceArm : ReflTransGen (Fire semantics continuation old tokens)
      (liveMark (pending semantics (Prefix.outerArm p.toRoutes arm))) (liveMark child) :=
    childSteps.lift (liveMark) (fun _ _ firing => .later (.advance firing))
  exact ⟨mark, (cut.prefix_reaches semantics old PUnit.unit reaches).trans
    (cut.tail_reaches semantics old PUnit.unit mark (((ReflTransGen.single firesRoute).tail entersArm).trans advanceArm))⟩

theorem waiting_reaches (arm : Fin 2)
    (chosen : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = arm)
    (child : Marking semantics (Prefix.outerArm p.toRoutes arm))
    (childSteps : ReflTransGen (Fire semantics (Prefix.outerArm p.toRoutes arm) (headerBank p.toRoutes old) PUnit.unit)
      (pending semantics (Prefix.outerArm p.toRoutes arm)) child) : Waiting p old arm child := by
  exact waiting_reaches_with p old (outerContinuation p) arm chosen child childSteps

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Proofs
