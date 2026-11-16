module

public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.Main
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Witness

/-!
# The trap witnesses of #669 are told apart by a resumable session

`pokePeekS` and `zeroS` (`Adequacy.Defs`) are `RefPubEquiv` (`witness_equiv`): on REF, nothing
runs after the trap of `poke`. The resumable session `poke, peek` resumes after that trap:
`pokePeekS` answers `trap, 1` (the global `poke` set before its lift trapped persists), which
`zeroS` never answers (`witness_session`). Hence they are not `RefSessEquiv`
(`witness_not_sessEquiv`), at every deterministic profile and component choice profile.

The session outcome comes from the IR play `poke · trap · peek · 1` (`pp_trapRounds`) through
session completeness (`sess_complete`); its absence for `zeroS` from session soundness
(`sess_sound`) and `z_not_trapRounds`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- The calls `poke, peek` of the witnesses. -/
def pokePeekCalls (c : Simple) (h : 1 < c.exports.length) :
    List (Fin c.exports.length × List IVal) :=
  [(⟨0, Nat.lt_of_succ_lt h⟩, []), (⟨1, h⟩, [])]

/-- The session outcomes `trap, 1`. -/
def trapThenOne : List (Option (List IVal)) := [none, some [.u32 1]]

theorem typed_pp : TypedCalls pokePeekS (pokePeekCalls pokePeekS (by decide)) := by
  intro q hq
  simp only [pokePeekCalls, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl <;> rfl

theorem typed_z : TypedCalls zeroS (pokePeekCalls zeroS (by decide)) := by
  intro q hq
  simp only [pokePeekCalls, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl <;> rfl

/-- **The session `poke, peek` answers `trap, 1` for `pokePeekS` and not for `zeroS`.** -/
theorem witness_session (o : Silmaril.Wasm.SingleThreaded.GrowOracle) (prof : ProfileKind) :
    refOuts trapThenOne ∈ sessObs (Silmaril.Wasm.SingleThreaded.profile o) prof pokePeekS
        (pokePeekCalls pokePeekS (by decide)) ∧
      refOuts trapThenOne ∉ sessObs (Silmaril.Wasm.SingleThreaded.profile o) prof zeroS
        (pokePeekCalls zeroS (by decide)) := by
  refine ⟨sess_complete _ prof pokePeekS pokePeekS_adequate _ _ typed_pp rfl ?_, ?_⟩
  · rw [sessMoves_eq]
    exact pp_trapRounds
  · intro h
    obtain ⟨outs, he, -, hmv⟩ := sess_sound _ prof zeroS zeroS_adequate _ typed_z h
    obtain rfl := refOuts_inj he
    rw [sessMoves_eq] at hmv
    exact z_not_trapRounds hmv (sessRoundsN_forget _ _ _)

/-- **The witnesses are not session-equivalent.** -/
theorem witness_not_sessEquiv (o : Silmaril.Wasm.SingleThreaded.GrowOracle) (prof : ProfileKind) :
    ¬ RefSessEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof pokePeekS zeroS := by
  intro h
  obtain ⟨hp, hn⟩ := witness_session o prof
  rw [h.obs _ typed_pp] at hp
  exact hn hp

end Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
