module

public import Silmaril.Wasm.Component.InstRef.Defs
public import Silmaril.Proofs.Wasm.Component.InstLitmus.Export

/-!
# Start functions in the instantiating IR: the reference litmus components

Plays of `SimpleI.toComp` (imports through `canon lower`, exports through `canon lift`) under
`Comp.denI (core3SemI P)`, for every profile:

* `callSI_inst`: instantiating `callSI` makes the host call `f(u32 1)`, answered `()`, and is
  ready;
* `globSI_get`: `globSI` is ready at once (no instantiation calls), and `get()` is answered
  `u32 42`;
* `trapSI_inst`: the instantiation of `trapSI` fails.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstRef

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstRef
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Proofs.Wasm.Component.InstLitmus
open Silmaril.Wasm.Numerics (Profile)

variable (P : Profile)

/-- The start function's call `f(1)` through `canon lower`: the host call `f(u32 1)`. -/
def fL : Round sigU (sigN 1) := ⟨(⟨0, by decide⟩, .flat [Flat.i32 1]), [⟨fV, unitV⟩], unitA⟩

theorem lower_runs (e : Nat) (he : 0 < e) :
    Prog.Runs (implsN e (SimpleI.lowerArgs hostI) 1 fL.q) fL.cs fL.a := by
  simp only [implsN, implsH, SimpleI.lowerArgs, hostI, List.mapIdx_cons, List.mapIdx_nil,
    fL, List.getElem?_cons_zero, Impl.prog, runChain, Target.prog, he, ↓reduceIte]
  exact .call (.pure _)

theorem callSI_node :
    (instRound (F := sigU) [⟨fV, unitV⟩] InstAns.ready).moves ∈
      coreNodeI (core3SemI P) hostI.length (callMod 1) (SimpleI.lowerArgs hostI) := by
  have := coreNodeI_inst (core3SemI P) hostI.length (callMod 1) (SimpleI.lowerArgs hostI) [fL]
    InstAns.ready (callMod_inst P callPrep_one) (by
      intro x hx
      obtain rfl := List.mem_singleton.1 hx
      exact lower_runs hostI.length Nat.zero_lt_one)
  simpa only [allCalls, fL, List.append_nil] using this

/-- **The instantiation of `callSI` makes the host call `f(u32 1)`.** -/
theorem callSI_inst :
    (instRound (F := sigU) [⟨fV, unitV⟩] InstAns.ready).moves ∈
      callSI.toComp.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have hb := withReady_maskH_rounds hostI.length [(fV, unitV)] (by
    intro z hz
    obtain rfl := List.mem_singleton.1 hz
    exact Nat.zero_lt_one)
  have h := extI_inst (e := hostI.length)
    (N := coreNodeI (core3SemI P) hostI.length (callMod 1) (SimpleI.lowerArgs hostI))
    [] [hostRound fV unitV] [] InstAns.ready (by simpa using hb)
    (by simpa [hostRound, Round.call] using callSI_node P) (by simp)
  simp only [roundsMoves, allCalls, hostRound, List.map_nil, List.nil_append,
    List.append_nil] at h
  exact h

theorem lift_runs :
    Prog.Runs (liftH (R := Unit) (exportsH (envAfter globSI.imports.length
      [.core globSI.mod (SimpleI.lowerArgs globSI.imports)]) (globSI.toComp.exports))
      (some (0, .vals []))) [⟨some (0, .flat []), a42⟩] (some (.vals [.u32 42])) := by
  simp only [liftH, exportsH, implsH, SimpleI.toComp, globSI, Comp.exports, List.map_cons,
    List.map_nil, List.getElem?_cons_zero, Impl.prog, runChain]
  exact .call (.pure _)

/-- **`globSI` is ready at once, and `get()` is answered `u32 42`.** -/
theorem globSI_get :
    roundsMoves [instRound (F := sigU) (X := sigU) [] .ready,
      exRound (R := Unit) (⟨(0, .vals []), [], some (.vals [.u32 42])⟩ : Round sigU sigU)] ∈
      globSI.toComp.denI (core3SemI P) := by
  refine denI_of_denNodesI_ex (core3SemI P) [] [.core globMod (SimpleI.lowerArgs [])] _ []
    (r := 0) (pl' := .flat []) (a := a42) lift_runs ?_
  simp only [denNodesI, Node.denI]
  have h := extI_inst_right (e := 0) (D := withReady (Strategy.ofHandler (maskH 0)))
    (N := coreNodeI (core3SemI P) 0 globMod (SimpleI.lowerArgs [])) [] []
    [⟨(0, .flat []), [], a42⟩] (by simp) (by simpa using base0_rounds)
    (globNode_play P 0)
  simpa [roundsMoves, allCalls, shiftRound, exRound] using h

/-- **The instantiation of `trapSI` fails.** -/
theorem trapSI_inst :
    (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈
      trapSI.toComp.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have hN : (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈
      coreNodeI (core3SemI P) 0 trapMod (SimpleI.lowerArgs []) := by
    have := coreNodeI_inst (core3SemI P) 0 trapMod (SimpleI.lowerArgs []) [] (InstAns.fail ())
      (trapMod_inst P) (by simp)
    simpa only [allCalls] using this
  have h₁ := extI_inst (e := 0) (N := coreNodeI (core3SemI P) 0 trapMod (SimpleI.lowerArgs []))
    [] [] [] (InstAns.fail ()) (by simpa using base0_rounds) (by simpa using hN) (by simp)
  simp only [roundsMoves, allCalls, List.map_nil, List.append_nil] at h₁
  exact h₁

end Silmaril.Proofs.Wasm.Component.InstRef
