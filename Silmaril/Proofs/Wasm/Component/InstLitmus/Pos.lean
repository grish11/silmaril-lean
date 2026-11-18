module

public import Silmaril.Proofs.Wasm.Component.InstLitmus.Core3

/-!
# Instantiation litmus components: instantiation plays

For every profile `P`, plays of `Comp.denI (core3SemI P)` assembled layer by layer
(`Silmaril.Proofs.Wasm.Component.InstSem.Run`) from the start runs of the modules (`Core3`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstLitmus

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Wasm.Numerics (Profile)

variable (P : Profile)

/-- The host's `f(k)` round: forwarded to the import. -/
abbrev fR (k : BitVec 32) : Round sigU sigU := hostRound (fQ k) unitA

/-- The call of `callMod k`'s start function, at the module's interface. -/
def fM (k : BitVec 32) : Round sigU (sigN 1) := ⟨(⟨0, by decide⟩, .flat [Flat.i32 k]), [⟨fQ k, unitA⟩], unitA⟩

theorem fwd0_runs (e : Nat) (he : 0 < e) (k : BitVec 32) :
    Prog.Runs (implsN e [Impl.fwd 0] 1 (fM k).q) (fM k).cs (fM k).a := by
  show Prog.Runs (Target.prog e (.call 0) (.flat [Flat.i32 k])) _ _
  simp only [Target.prog, he, ↓reduceIte]
  exact .call (.pure _)

/-- **The start function of `callMod k` calls `f(k)`: its instantiation round.** -/
theorem callMod_inst {k : BitVec 32} (h : prepOk 1 (callStoreOk k) (callPrep k) = true) :
    (instRound (F := sigN 0) [(fM k).call] InstAns.ready).moves ∈ (core3SemI P).sem (callMod k) := by
  show _ ∈ engineStrategyI (core3P P) (instOfI (core3P P) (callMod k).mod (callMod k).imports
    (callMod k).exports) (callMod k).imports (callMod k).exports
  rw [instOfI_call P h]
  obtain ⟨_, -, hs⟩ := prepOk_eq h
  obtain ⟨t, hr, hco, ⟨t', hr', hf⟩, -⟩ := call_start (P := P) hs
  refine engine_inst_ready (c' := (storeOf (callPrep k), t')) rfl rfl ?_ hf
  exact .call hr hco (show 0 < (callMod k).imports.length from Nat.zero_lt_one) unitA
    (.nil hr')

/-- **The start function of `trapMod` traps: instantiation fails.** -/
theorem trapMod_inst :
    (instRound (F := sigN 1) (X := sigN 0) [] (InstAns.fail ())).moves ∈
      (core3SemI P).sem trapMod := by
  show _ ∈ engineStrategyI (core3P P) (instOfI (core3P P) trapMod.mod trapMod.imports
    trapMod.exports) trapMod.imports trapMod.exports
  rw [instOfI_trap P]
  obtain ⟨_, -, hs⟩ := prepOk_eq trapPrep_ok.1
  obtain ⟨t, hr, hf⟩ := trap_start (P := P) hs
  exact engine_inst_fail (c' := (storeOf trapPrep, t)) rfl rfl (.nil hr) hf

/-- **`getMod` has no start function: it is ready at once.** -/
theorem getMod_inst :
    (instRound (F := sigN 1) (X := sigN 0) [] InstAns.ready).moves ∈ (core3SemI P).sem getMod := by
  show _ ∈ engineStrategyI (core3P P) (instOfI (core3P P) getMod.mod getMod.imports
    getMod.exports) getMod.imports getMod.exports
  rw [instOfI_get P]
  exact engine_noStart_ready rfl rfl

theorem callNode_inst {k : BitVec 32} (h : prepOk 1 (callStoreOk k) (callPrep k) = true)
    (e : Nat) (he : 0 < e) :
    (instRound (F := sigU) [⟨fQ k, unitA⟩] InstAns.ready).moves ∈
      coreNodeI (core3SemI P) e (callMod k) [Impl.fwd 0] := by
  have := coreNodeI_inst (core3SemI P) e (callMod k) [Impl.fwd 0] [fM k] InstAns.ready
    (callMod_inst P h) (by
      intro x hx
      obtain rfl := List.mem_singleton.1 hx
      exact fwd0_runs e he k)
  simpa only [allCalls, fM, List.append_nil] using this

/-- The imports, ready at once, forwarding the host calls `ks`. -/
theorem base_rounds (ks : List (BitVec 32)) :
    roundsMoves (instRound (F := sigU) [] .ready :: (ks.map fR).map exRound) ∈
      withReady (R := Unit) (Strategy.ofHandler (maskH hostI.length)) := by
  have h := withReady_maskH_rounds hostI.length (ks.map fun k => (fQ k, unitA))
    (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨k, -, rfl⟩ := hz
      exact Nat.zero_lt_one)
  simpa only [List.map_map, Function.comp_def] using h

/-- **(b)** -/
theorem oneC_inst :
    (instRound (F := sigU) [⟨fQ 1, unitA⟩] InstAns.ready).moves ∈ oneC.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have h := extI_inst (e := hostI.length) (N := coreNodeI (core3SemI P) hostI.length (callMod 1) [Impl.fwd 0])
    [] [fR 1] [] InstAns.ready (by simpa using base_rounds [1])
    (by simpa [hostRound, Round.call] using callNode_inst P callPrep_one hostI.length Nat.zero_lt_one) (by simp)
  simpa [roundsMoves, allCalls, hostRound] using h

/-- **(a)** -/
theorem twoC_inst :
    (instRound (F := sigU) [⟨fQ 1, unitA⟩, ⟨fQ 2, unitA⟩] InstAns.ready).moves ∈
      twoC.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have h₁ := extI_inst (e := hostI.length)
    (N := coreNodeI (core3SemI P) hostI.length (callMod 1) [Impl.fwd 0])
    [] [fR 1] [fR 2] InstAns.ready (by simpa using base_rounds [1, 2])
    (by simpa [hostRound, Round.call] using callNode_inst P callPrep_one hostI.length Nat.zero_lt_one)
    (by intro z hz; simp at hz; subst hz; decide)
  have h₂ := extI_inst (D := extI hostI.length
      (withReady (Strategy.ofHandler (maskH hostI.length)))
      (coreNodeI (core3SemI P) hostI.length (callMod 1) [Impl.fwd 0]))
    (e := hostI.length + Node.width (Node.core (callMod 1) [Impl.fwd 0]))
    (N := coreNodeI (core3SemI P) (hostI.length + Node.width (Node.core (callMod 1)
      [Impl.fwd 0])) (callMod 2) [Impl.fwd 0])
    [⟨fQ 1, unitA⟩] [fR 2] [] InstAns.ready
    (by simpa [roundsMoves, allCalls, hostRound] using h₁)
    (by simpa [hostRound, Round.call] using (callNode_inst P callPrep_two
      (hostI.length + Node.width (Node.core (callMod 1) [Impl.fwd 0])) Nat.zero_lt_one)) (by simp)
  simpa [roundsMoves, allCalls, hostRound] using h₂

/-- **(c)** -/
theorem trapC_inst :
    (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈ trapC.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have hN : (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈
      coreNodeI (core3SemI P) hostI.length trapMod [] := by
    have := coreNodeI_inst (core3SemI P) hostI.length trapMod [] [] (InstAns.fail ()) (trapMod_inst P)
      (by simp)
    simpa only [allCalls] using this
  have h₁ := extI_inst (e := hostI.length) (N := coreNodeI (core3SemI P) hostI.length trapMod [])
    [] [] [] (InstAns.fail ()) (by simpa using base_rounds []) (by simpa using hN) (by simp)
  exact extI_fail [] () (by simpa [roundsMoves, allCalls] using h₁)

/-- **(d)** -/
theorem hiddenC_inst :
    (instRound (F := sigU) [⟨fQ 1, unitA⟩] InstAns.ready).moves ∈ hiddenC.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have h₁ := extI_inst (e := hostI.length)
    (N := coreNodeI (core3SemI P) hostI.length (callMod 1) [Impl.fwd 0])
    [] [fR 1] [] InstAns.ready (by simpa using base_rounds [1])
    (by simpa [hostRound, Round.call] using callNode_inst P callPrep_one hostI.length Nat.zero_lt_one) (by simp)
  have hN : (instRound (F := sigU) (X := sigU) [] InstAns.ready).moves ∈
      coreNodeI (core3SemI P) (hostI.length + Node.width (Node.core (callMod 1) [Impl.fwd 0]))
        getMod [] := by
    have := coreNodeI_inst (core3SemI P)
      (hostI.length + Node.width (Node.core (callMod 1) [Impl.fwd 0])) getMod [] [] InstAns.ready
      (getMod_inst P) (by simp)
    simpa only [allCalls] using this
  have h₂ := extI_inst (e := hostI.length + Node.width (Node.core (callMod 1) [Impl.fwd 0]))
    [⟨fQ 1, unitA⟩] [] [] InstAns.ready (by simpa [roundsMoves, allCalls, hostRound] using h₁)
    (by simpa using hN) (by simp)
  simpa [roundsMoves, allCalls] using h₂

end Silmaril.Proofs.Wasm.Component.InstLitmus
