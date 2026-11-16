module

public import Silmaril.Wasi.Component.Consequence.Signed.Defs
public import Silmaril.Wasi.Component.Consequence.Gentzen.Thms
public import Silmaril.Wasm.Examples.MemberCheck.Thms
public import Silmaril.Wasm.Examples.EmptyCheck.Thms
import Silmaril.Proofs.Wasi.Component.Consequence.Signed

/-! # Signed and two-sided observation protocols: theorems

* `accepted_swap`: `swap` exchanges the sides of acceptance.
* **Batches as raw Gentzen readings**: `batchUnsat` and `batchTaut` are `viaUnsat` and `viaTauto` of
  the emitted batches (`batchUnsat_iff`, `batchTaut_iff`). A sound UNSAT (TAUTO) emitter gives
  valid sequents under the matching negation law, and so does the Gentzen closure of its reading
  (`batchUnsat_le_valid`, `derives_batchUnsat_le_valid`, `batchTaut_le_valid`,
  `derives_batchTaut_le_valid`). Soundness of the emitter is always a hypothesis.
* **The finite-set lift**: every emitted list gives its member set (`batchFinset_of_batches`), and
  a sound UNSAT emitter stays sound on the sets (`batchFinset_unsat`), since unsatisfiability
  depends only on members. Nothing says the lift loses nothing.
* **Core modules through an explicit codec**: through `memberEnc`, `MemberCheck` derives only
  `Γ ⊢ [c]` with `c ∈ Γ`, for every host set (`coreSeq_member_sound`), and exactly those below the
  ABI bound for a nonempty host set (`coreSeq_member_iff`). It is complete only on singleton
  succedents: nothing else is encoded (`coreSeq_member_not_singleton`). `EmptyCheck` derives
  nothing, through any codec (`coreSeq_empty`).

Proofs: `Silmaril.Proofs.Wasi.Component.Consequence.Signed`.
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (Signed)
open Silmaril.Consequence.Gentzen
open Silmaril.Consequence.Refutation (Unsat CheckSound)

universe u v

variable {X : Type u} {C : Type v} {F M : Type} {T : Set (List WEv)}

theorem accepted_swap {r : Reading X C} {x : X} {c : C} :
    Accepted T (swap r) c x ↔ Accepted T r x c :=
  Proofs.Wasi.Component.Consequence.accepted_swap

/-! ## Batches -/

variable {r : Reading (List F) Unit} {neg : F → F} {sat : M → F → Prop}

theorem batchUnsat_iff {Γ Δ : List F} : batchUnsat T r neg Γ Δ ↔ predOf T r (Γ ++ Δ.map neg) :=
  accepted_swap

theorem batchTaut_iff {Γ Δ : List F} : batchTaut T r neg Γ Δ ↔ predOf T r (Γ.map neg ++ Δ) :=
  accepted_swap

/-- **A sound UNSAT emitter gives valid sequents.** -/
theorem batchUnsat_le_valid (hs : CheckSound sat (predOf T r)) (hn : NegComplete sat neg) :
    batchUnsat T r neg ≤ Valid sat :=
  unsatSeq_le_valid (fun Γ h => hs Γ (accepted_swap.1 h)) hn

theorem derives_batchUnsat_le_valid (hs : CheckSound sat (predOf T r))
    (hn : NegComplete sat neg) : Derives defaultRules (batchUnsat T r neg) ≤ Valid sat :=
  derives_le_valid (batchUnsat_le_valid hs hn)

/-- **A sound TAUTO emitter gives valid sequents.** -/
theorem batchTaut_le_valid (hs : TautSound sat (predOf T r)) (hn : NegSound sat neg) :
    batchTaut T r neg ≤ Valid sat :=
  tautSeq_le_valid (fun Δ h => hs Δ (accepted_swap.1 h)) hn

theorem derives_batchTaut_le_valid (hs : TautSound sat (predOf T r)) (hn : NegSound sat neg) :
    Derives defaultRules (batchTaut T r neg) ≤ Valid sat :=
  derives_le_valid (batchTaut_le_valid hs hn)

/-! ## The finite-set lift -/

theorem batchFinset_of_batches {V : Type} [DecidableEq V] {r : Reading (List (Signed V)) Unit}
    {l : List (Signed V)} (h : batches T r l) : batchFinset T r l.toFinset :=
  ⟨l, rfl, h⟩

/-- **A sound UNSAT emitter is sound on member sets.** -/
theorem batchFinset_unsat {V : Type} [DecidableEq V] {sat : M → Signed V → Prop}
    {r : Reading (List (Signed V)) Unit} (hs : CheckSound sat (batches T r))
    {s : Finset (Signed V)} (h : batchFinset T r s) : Unsat sat s.toList :=
  Proofs.Wasi.Component.Consequence.batchFinset_unsat hs h

/-! ## Core modules -/

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (HostSemantics)

/-- **`MemberCheck` through `memberEnc` is sound**, for every host set. -/
theorem coreSeq_member_sound (P : Profile) (Hosts : Set (HostSemantics Nat)) {Γ Δ : List UInt8}
    (h : coreSeq P Hosts Silmaril.Wasm.Examples.MemberCheck.prog "check" memberEnc Γ Δ) :
    ∃ c, Δ = [c] ∧ c ∈ Γ := by
  obtain ⟨w, hw, ha⟩ := h
  obtain ⟨c, rfl, rfl⟩ := Proofs.Wasi.Component.Consequence.memberEnc_eq_some.1 hw
  obtain ⟨_, _, he, hm⟩ := Silmaril.Wasm.Examples.MemberCheck.exportAccepted_subset P Hosts ha
  cases he
  exact ⟨_, rfl, hm⟩

/-- **…and exact below the ABI bound**, for a nonempty host set. -/
theorem coreSeq_member_iff (P : Profile) {Hosts : Set (HostSemantics Nat)} (hH : Hosts.Nonempty)
    {Γ Δ : List UInt8} (hl : Γ.length + 1 < 2 ^ 32) :
    coreSeq P Hosts Silmaril.Wasm.Examples.MemberCheck.prog "check" memberEnc Γ Δ ↔
      ∃ c, Δ = [c] ∧ c ∈ Γ := by
  refine ⟨coreSeq_member_sound P Hosts, ?_⟩
  rintro ⟨c, rfl, hc⟩
  refine ⟨c :: Γ, rfl, ?_⟩
  rw [Silmaril.Wasm.Examples.MemberCheck.exportAccepted_eq P hH]
  exact ⟨⟨c, Γ, rfl, hc⟩, by simpa using hl⟩

/-- Only singleton succedents are encoded: the adapter is not complete for other sequents. -/
theorem coreSeq_member_not_singleton (P : Profile) (Hosts : Set (HostSemantics Nat))
    {Γ Δ : List UInt8} (hΔ : ∀ c, Δ ≠ [c]) :
    ¬ coreSeq P Hosts Silmaril.Wasm.Examples.MemberCheck.prog "check" memberEnc Γ Δ :=
  fun h => let ⟨c, he, _⟩ := coreSeq_member_sound P Hosts h; hΔ c he

/-- **`EmptyCheck` derives nothing**, through any codec and for every host set. -/
theorem coreSeq_empty (P : Profile) (Hosts : Set (HostSemantics Nat))
    (enc : List UInt8 → List UInt8 → Option (List UInt8)) :
    coreSeq P Hosts Silmaril.Wasm.Examples.EmptyCheck.prog "check" enc = ⊥ := by
  funext Γ Δ
  simp [coreSeq, Silmaril.Wasm.Examples.EmptyCheck.exportAccepted_eq_empty]

end Silmaril.Wasi.Consequence
