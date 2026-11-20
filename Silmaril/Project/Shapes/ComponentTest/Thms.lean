module

public import Silmaril.Project.Shapes.ComponentTest.Defs

/-! # Standard problem shapes: component tests (consequences)

* `Instantiates.lowered`, `InstTraps.lowered`, `ExportReturnsAfterInst.lowered`: the binary
  lowers to one component (the parse is a function);
* `Instantiates.unique`: at a deterministic profile, a complete instantiation answered by the
  host is the trace, then `ready`;
* `InstTraps.not_ready`, `InstTraps.no_exports`: at a deterministic profile, under the host, the
  instantiation never succeeds and no export is answered; `InstTraps.no_calls`: with the empty
  trace, no import call is ever made;
* `ExportReturnsAfterInst.denX`: in the export phase `Comp.denX`, `q` is answered `v`;
  `ExportReturnsAfterInst.instantiates_play`: the instantiation play `[inst] ++ tr ++ [ready]`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.ComponentTest

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {b : ByteArray} {host : sigU.Op → Option Payload} {tr : List Call}

theorem Instantiates.lowered (h : Instantiates b host tr) :
    ∃ c, (Binary.parseComponent b).toOption = some c := by
  obtain ⟨c, hc, -⟩ := h
  exact ⟨c, by rw [hc]; rfl⟩

theorem Instantiates.unique (h : Instantiates b host tr) {c : Comp Binary.CoreMod}
    (hc : Binary.parseComponent b = .ok c) (o : GrowOracle) {cs : List Call} {a : InstAns Unit}
    (hp : instPlay (F := sigU) cs a ∈ c.denI (Binary.coreModSemI (profile o)))
    (hh : TraceOf host cs) : cs = tr ∧ a = .ready := by
  obtain ⟨c', hc', -, -, h⟩ := h
  obtain rfl : c' = c := Except.ok.inj (hc'.symm.trans hc)
  exact (h o).2 cs a hp hh

theorem InstTraps.lowered (h : InstTraps b host tr) :
    ∃ c, (Binary.parseComponent b).toOption = some c := by
  obtain ⟨c, hc, -⟩ := h
  exact ⟨c, by rw [hc]; rfl⟩

theorem InstTraps.not_ready (h : InstTraps b host tr) {c : Comp Binary.CoreMod}
    (hc : Binary.parseComponent b = .ok c) (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ c.denI (Binary.coreModSemI (profile o))) (hh : HostAnswers host p) :
    ansInst .ready ∉ p := by
  obtain ⟨c', hc', -, -, h⟩ := h
  obtain rfl : c' = c := Except.ok.inj (hc'.symm.trans hc)
  exact ((h o p hp).2 hh).1

theorem InstTraps.no_exports (h : InstTraps b host tr) {c : Comp Binary.CoreMod}
    (hc : Binary.parseComponent b = .ok c) (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ c.denI (Binary.coreModSemI (profile o))) (hh : HostAnswers host p)
    (q : sigU.Op) (r : Option Payload) : ansEx q r ∉ p := by
  obtain ⟨c', hc', -, -, h⟩ := h
  obtain rfl : c' = c := Except.ok.inj (hc'.symm.trans hc)
  exact ((h o p hp).2 hh).2 q r

theorem InstTraps.no_calls (h : InstTraps b host []) {c : Comp Binary.CoreMod}
    (hc : Binary.parseComponent b = .ok c) (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ c.denI (Binary.coreModSemI (profile o))) : lowerAsks p = [] := by
  obtain ⟨c', hc', -, -, h⟩ := h
  obtain rfl : c' = c := Except.ok.inj (hc'.symm.trans hc)
  exact List.prefix_nil.1 (h o p hp).1

theorem ExportReturnsAfterInst.lowered {q : sigU.Op} {v : Option Payload}
    (h : ExportReturnsAfterInst b host tr q v) :
    ∃ c, (Binary.parseComponent b).toOption = some c := by
  obtain ⟨c, hc, -⟩ := h
  exact ⟨c, by rw [hc]; rfl⟩

theorem ExportReturnsAfterInst.instantiates_play {q : sigU.Op} {v : Option Payload}
    (h : ExportReturnsAfterInst b host tr q v) {c : Comp Binary.CoreMod}
    (hc : Binary.parseComponent b = .ok c) (P : Profile) :
    instPlay (F := sigU) tr .ready ∈ c.denI (Binary.coreModSemI P) := by
  obtain ⟨c', hc', -, hP, -⟩ := h
  obtain rfl : c' = c := Except.ok.inj (hc'.symm.trans hc)
  exact (c'.denI _).of_prefix (hP P) (List.prefix_append _ _)

theorem ExportReturnsAfterInst.denX {q : sigU.Op} {v : Option Payload}
    (h : ExportReturnsAfterInst b host tr q v) {c : Comp Binary.CoreMod}
    (hc : Binary.parseComponent b = .ok c) (P : Profile) :
    ([.inr (.ask q), .inr (.ans q v)] : List (Move sigU sigU)) ∈
      c.denX (Binary.coreModSemI P) := by
  obtain ⟨c', hc', -, hP, -⟩ := h
  obtain rfl : c' = c := Except.ok.inj (hc'.symm.trans hc)
  exact Strategy.subset_generate ⟨tr, hP P⟩ ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩

end Silmaril.Project.Shapes.ComponentTest
