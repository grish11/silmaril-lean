module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation

open CategoryTheory
open SeaOfNodes.Loop (Incoming)
open RVSDG (Port)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open Silmaril.MLIR.MemRef (Buffer)
open MLIR.MemRef.CF (Label)
open Memory.Diamond.Institution (reduct pullInput_get)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

private abbrev words : EntrySignature := ⟨[.word, .word, .word]⟩
private abbrev scope : EntrySignature := ⟨.address :: .address :: words.args⟩
private def first : Port scope.args .address := .head
private def second : Port scope.args .address := .tail .head
private def capturedWords : words ⟶ scope := ⟨fun p => .tail (.tail p)⟩

-- The two selections are independent typed bindings at each occurrence.
private def wiring (arrival : Incoming) : scope ⟶ scope :=
  bindAddress (arrival.select first second)
    (bindAddress (arrival.select second first) capturedWords)

private def swapPorts : scope ⟶ scope := wiring .backedge

private def identifyPorts : scope ⟶ scope :=
  bindAddress first (bindAddress first capturedWords)

private def body : Memory.Graph scope.args :=
  .load (.latest 0) (.arg first)
    (.store (.latest 0) (.arg first) (.arg (.tail (.tail .head)))
      (.store (.latest 1) (.arg second) (.arg (.tail (.tail (.tail .head))))
        (.ret (.latest 2) (.output 0 .head))))

private def graph : Graph scope.args :=
  ⟨body, rfl, .tail (.tail (.tail (.tail .head)))⟩

private def model (stop : Word) : EntryModel scope :=
  ⟨3, .cons (0 : Address 3) (.cons (1 : Address 3) (.cons (9 : Word) (.cons (5 : Word) (.cons stop .nil))))⟩

private def initial : Heap 3 := fun address => if address = 2 then 99 else 0
private def written : Heap 3 := (initial.write 0 9).write 1 5
private def reversed : Heap 3 := (initial.write 1 9).write 0 5

private theorem header_entry :
    memrefHeader graph (reduct (wiring .entry) (model 0)) initial =
      (.inl ⟨Label.exit, .cons 0 .nil⟩, ⟨written⟩) := by
  refine (memrefHeader_step graph (reduct (wiring .entry) (model 0)) initial).trans ?_
  rfl

private theorem header_swapped :
    memrefHeader graph (reduct (wiring .entry) (reduct swapPorts (model 0))) initial =
      (.inl ⟨Label.exit, .cons 0 .nil⟩, ⟨reversed⟩) := by
  refine (memrefHeader_step graph (reduct (wiring .entry) (reduct swapPorts (model 0))) initial).trans ?_
  rfl

-- A single activation with the feedback column yields the same frame as
-- the entry column after renaming both captured address ports.
example :
    petriActivation (mapGraph (wiring .backedge) graph) (model 0) initial reversed false := by
  have ports : wiring .entry ≫ swapPorts = wiring .backedge := by
    apply congrArg EntrySignature.Hom.mk
    funext sort port
    cases port with
    | head => rfl
    | tail p => cases p <;> rfl
  rw [← ports]
  exact (petri_comp_iff_memref_header (wiring .entry) swapPorts graph (model 0) initial reversed false).mpr
    header_swapped

example : petriActivation (mapGraph (wiring .entry) graph) (model 0) initial written false :=
  (petri_map_iff_memref_header (wiring .entry) graph (model 0) initial written false).mpr header_entry

-- A word-only comparison would miss the changed first cell.
example : written ≠ reversed := by
  intro equal
  exact (by decide : (9 : Word) ≠ 5) (congrFun equal 0)

-- Identifying the two captured addresses erases the column distinction
-- in the emitted tables. Each pulled-back valuation has coincident ports.
example : mapGraph (wiring .entry ≫ identifyPorts) graph =
    mapGraph (wiring .backedge ≫ identifyPorts) graph := rfl

example (target : EntryModel scope) :
    (reduct identifyPorts target).input.get first = (reduct identifyPorts target).input.get second := by
  change (Memory.Diamond.Institution.pullInput (EntrySignature.Hom.port identifyPorts) target.input).get first =
    (Memory.Diamond.Institution.pullInput (EntrySignature.Hom.port identifyPorts) target.input).get second
  simp only [pullInput_get]
  rfl

-- With the feedback column fixed, the already implemented whole-loop
-- emitters admit a finite completion, each with its own witness.
private theorem observed : MLIR.MemRef.CF.Institution.observe graph (reduct (wiring .backedge) (model 0)) initial =
    Part.some (0, reversed) := by
  let pulled := reduct (wiring .backedge) (model 0)
  have returned : graph.Returns pulled.input initial 0 reversed :=
    ⟨0, (graph.returnsAfter_iff_evalAfter pulled.input initial 0 0 reversed).mpr rfl⟩
  exact (MLIR.MemRef.CF.Institution.observe_eq graph pulled initial).trans
    (Part.eq_some_iff.mpr ((graph.returns_iff_mem_denote pulled.input initial 0 reversed).mp returned))

example : Finishes (thetaRuntime 3) (mapGraph (wiring .backedge) graph).lowerTheta
    (encodeInput initial (model 0).input) (encodeResult 0 reversed) :=
  (petri_completion_map_iff_memref (wiring .backedge) graph (model 0) initial 0 reversed).mpr observed

private theorem fixed :
    (mapGraph (wiring .entry) graph).step (model 7).input written = .inr written := by
  change Sum.inr ((written.write 0 9).write 1 5) = Sum.inr written
  apply congrArg Sum.inr
  funext address
  by_cases one : address = 1
  · subst address
    simp [Heap.write, written]
  · by_cases zero : address = 0
    · subst address
      simp [Heap.write, written]
    · simp [Heap.write, one, zero]

example : MLIR.MemRef.CF.Institution.observe graph (reduct (wiring .entry) (model 7)) written = Part.none := by
  apply (petri_no_completion_map_iff_memref (wiring .entry) graph (model 7) written).mp
  intro output completed
  obtain ⟨fuel, returned⟩ := (finishes_iff _ _ _ _).mp completed
  have absent := (mapGraph (wiring .entry) graph).lowerTheta_run_none_of_fixed_backedge
    (model 7).input written fixed fuel
  cases absent.symm.trans returned

private def cells (buffer : Buffer 3) : Word × Word × Word :=
  (buffer.cell 0, buffer.cell 1, buffer.cell 2)

#guard cells (memrefHeader graph (reduct (wiring .entry) (model 0)) initial).2 == (9, 5, 99)
#guard cells (memrefHeader graph (reduct (wiring .backedge) (model 0)) initial).2 == (5, 9, 99)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation
