module

public import Silmaril.Wasm.Component.InstTests.Defs
public import Silmaril.Proofs.Wasm.Component.InstLitmus.Export

/-!
# Component test binaries: the plays, at every profile

Plays of `Comp.denI (core3SemI P)` of `startsC` and `trapLC`, assembled node by node from the
start runs of the litmus modules (`Silmaril.Proofs.Wasm.Component.InstLitmus`), with the import
`f` wired through `canon lower` (`lowF`) and the export `get` through `canon lift` (`getL`):

* `lowF_runs`: the start function's flat call `f(i32 k)` is the host call `f(u32 k)`, answered
  `()`;
* `starts_play`: `[inst, f(1), (), f(2), (), ready, get(), 42]`;
* `trap_play`: `[inst, fail ()]`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstTests

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Proofs.Wasm.Component.InstLitmus
open Silmaril.Wasm.Numerics (Profile)

variable (P : Profile)

/-- The start function's call `f(k)` through `canon lower`: the host call `f(u32 k)`. -/
def fL (k : BitVec 32) : Round sigU (sigN 1) :=
  ⟨(⟨0, Nat.zero_lt_one⟩, .flat [Flat.i32 k]), [⟨fV k, unitV⟩], unitA⟩

theorem lowF_runs (e : Nat) (he : 0 < e) (k : BitVec 32) :
    Prog.Runs (implsN e lowF 1 (fL k).q) (fL k).cs (fL k).a := by
  simp only [implsN, implsH, lowF, fL, List.getElem?_cons_zero, Impl.prog, runChain,
    Target.prog, he, ↓reduceIte]
  exact .call (.pure _)

theorem callNodeL_inst {k : BitVec 32} (h : prepOk 1 (callStoreOk k) (callPrep k) = true)
    (e : Nat) (he : 0 < e) :
    (instRound (F := sigU) [⟨fV k, unitV⟩] InstAns.ready).moves ∈
      coreNodeI (core3SemI P) e (callMod k) lowF := by
  have := coreNodeI_inst (core3SemI P) e (callMod k) lowF [fL k] InstAns.ready
    (callMod_inst P h) (by
      intro x hx
      obtain rfl := List.mem_singleton.1 hx
      exact lowF_runs e he k)
  simpa only [allCalls, fL, List.append_nil] using this

theorem getL_runs :
    Prog.Runs (liftH (R := Unit) (exportsH 2 [getL 1]) (some getV))
      [⟨some (1, .flat []), a42⟩] v42 := by
  simp only [liftH, exportsH, implsH, getL, getV, List.map_cons, List.map_nil,
    List.getElem?_cons_zero, Impl.prog, runChain]
  exact .call (.pure _)

/-- **`starts`: `f(1)`, `f(2)`, ready, then `get()` is answered `42`.** -/
theorem starts_play :
    roundsMoves [instRound (F := sigU) startsTrace .ready,
      exRound (R := Unit) (⟨getV, [], v42⟩ : Round sigU sigU)] ∈ startsC.denI (core3SemI P) := by
  refine denI_of_denNodesI_ex (core3SemI P) hostI
    [.core (callMod 1) lowF, .core (callMod 2) lowF, .core globMod []] [getL 1] startsTrace
    (r := 1) (pl' := .flat []) (a := a42) getL_runs ?_
  simp only [denNodesI, Node.denI]
  have hb := withReady_maskH_rounds hostI.length [(fV 1, unitV), (fV 2, unitV)] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> exact Nat.zero_lt_one)
  have h₁ := extI_inst (e := hostI.length)
    (N := coreNodeI (core3SemI P) hostI.length (callMod 1) lowF)
    [] [hostRound (fV 1) unitV] [hostRound (fV 2) unitV] InstAns.ready (by simpa using hb)
    (by simpa [hostRound, Round.call] using
      (callNodeL_inst P callPrep_one hostI.length Nat.zero_lt_one))
    (by intro z hz; simp at hz; subst hz; decide)
  have h₂ := extI_inst (D := extI hostI.length
      (withReady (Strategy.ofHandler (maskH hostI.length)))
      (coreNodeI (core3SemI P) hostI.length (callMod 1) lowF))
    (e := hostI.length + Node.width (Node.core (callMod 1) lowF))
    (N := coreNodeI (core3SemI P) (hostI.length + Node.width (Node.core (callMod 1) lowF))
      (callMod 2) lowF)
    [⟨fV 1, unitV⟩] [hostRound (fV 2) unitV] [] InstAns.ready
    (by simpa [roundsMoves, allCalls, hostRound] using h₁)
    (by simpa [hostRound, Round.call] using (callNodeL_inst P callPrep_two
      (hostI.length + Node.width (Node.core (callMod 1) lowF)) Nat.zero_lt_one)) (by simp)
  have h₃ := extI_inst_right
    (e := hostI.length + Node.width (Node.core (callMod 1) lowF) +
      Node.width (Node.core (callMod 2) lowF))
    (D := extI (hostI.length + Node.width (Node.core (callMod 1) lowF))
      (extI hostI.length (withReady (Strategy.ofHandler (maskH hostI.length)))
        (coreNodeI (core3SemI P) hostI.length (callMod 1) lowF))
      (coreNodeI (core3SemI P) (hostI.length + Node.width (Node.core (callMod 1) lowF))
        (callMod 2) lowF))
    (N := coreNodeI (core3SemI P) (hostI.length + Node.width (Node.core (callMod 1) lowF) +
      Node.width (Node.core (callMod 2) lowF)) globMod [])
    [⟨fV 1, unitV⟩, ⟨fV 2, unitV⟩] [] [⟨(0, .flat []), [], a42⟩] (by simp)
    (by simpa [roundsMoves, allCalls, hostRound] using h₂)
    (by simpa using globNode_play P _)
  simp only [roundsMoves, allCalls, shiftRound, exRound, startsTrace, List.map_cons,
    List.map_nil, List.append_nil] at h₃ ⊢
  exact h₃

/-- **`trap`: the instantiation fails at once.** -/
theorem trap_play :
    (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈ trapLC.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have hN : (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈
      coreNodeI (core3SemI P) hostI.length trapMod [] := by
    have := coreNodeI_inst (core3SemI P) hostI.length trapMod [] [] (InstAns.fail ())
      (trapMod_inst P) (by simp)
    simpa only [allCalls] using this
  have h₁ := extI_inst (e := hostI.length) (N := coreNodeI (core3SemI P) hostI.length trapMod [])
    [] [] [] (InstAns.fail ()) (by simpa using base_rounds []) (by simpa using hN) (by simp)
  exact extI_fail [] () (by simpa [roundsMoves, allCalls] using h₁)

end Silmaril.Proofs.Wasm.Component.InstTests
