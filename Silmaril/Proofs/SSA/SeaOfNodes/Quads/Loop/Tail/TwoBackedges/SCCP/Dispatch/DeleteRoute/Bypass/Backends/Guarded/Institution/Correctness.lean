module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Proofs

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)

variable {regs : List (ValueSort Width)} {result : Width}

theorem admit_self [BankDecidableEq Word (dataPorts regs)] (p : Admitted regs result) :
    admit p.source p.facts = .ok p := by
  unfold admit
  split
  next cert h =>
    have eq : cert = p.checked := Except.ok.inj (h.symm.trans p.admitted)
    cases p
    cases eq
    rfl
  next reason h =>
    cases h.symm.trans p.admitted

theorem emitted [BankDecidableEq Word (dataPorts regs)] (p : Admitted regs result) :
    Bypass.MLIR.CF.EntryGuard.compile p.source p.facts = .ok p.emit.cf ∧
      Bypass.Numbered.EntryGuard.compile p.source p.facts = .ok p.emit.numbered :=
  ⟨congrArg (Except.map Bypass.MLIR.CF.EntryGuard.lower) p.admitted,
    congrArg (Except.map Bypass.Numbered.EntryGuard.lower) p.admitted⟩

theorem returns_iff_source [BankDecidableEq Word (dataPorts regs)] (backend : Backend)
    (p : Admitted regs result) (input : Entry regs) (value : Word result) :
    backend.Returns p.emit input value ↔ SourceReturns p.source input value := by
  cases backend with
  | cf => exact Bypass.MLIR.CF.EntryGuard.compile_returns_iff (emitted p).1 input value
  | numbered => exact Bypass.Numbered.EntryGuard.compile_returns_iff (emitted p).2 input value
  | petri => exact Bypass.Numbered.EntryGuard.Petri.compile_finishes_iff (emitted p).2 input value

theorem mem_observe_source_iff [BankDecidableEq Word (dataPorts regs)]
    (p : Admitted regs result) (input : Entry regs) (value : Word result) :
    value ∈ p.observe input ↔ SourceReturns p.source input value :=
  Total.mem_sourcePart_iff.trans
    ⟨fun ⟨⟨fuel⟩, returned⟩ => ⟨fuel, returned⟩, fun ⟨fuel, returned⟩ => ⟨⟨fuel⟩, returned⟩⟩

private theorem mem_petriPart_iff (a : Artifacts regs result) (input : Entry regs) (value : Word result) :
    value ∈ a.petriPart input ↔ Backend.petri.Returns a input value := by
  rw [Artifacts.petriPart, Part.mem_mk_iff]
  constructor
  · rintro ⟨witness, rfl⟩
    exact Classical.choose_spec witness
  · intro completed
    let witness : ∃ word, Backend.petri.Returns a input word := ⟨value, completed⟩
    have picked := Classical.choose_spec witness
    obtain ⟨fuel, ran⟩ := (Bypass.Numbered.EntryGuard.Petri.finishes_iff_numbered a.numbered input
      (.cons (Classical.choose witness) .nil)).mp picked
    have packets := Bypass.Numbered.EntryGuard.Petri.completed_packet_eq a.numbered input completed ran
    exact ⟨witness, congrArg (fun packet : Tuple (Val Word) [.value (.data result)] => packet.get .head)
      packets.symm⟩

theorem mem_observe_iff (backend : Backend) (a : Artifacts regs result)
    (input : Entry regs) (value : Word result) :
    value ∈ backend.observe a input ↔ backend.Returns a input value := by
  cases backend with
  | cf => exact Total.mem_observeCF_iff a.cf
  | numbered => exact Total.mem_observeNumbered_iff a.numbered.2
  | petri => exact mem_petriPart_iff a input value

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Proofs
