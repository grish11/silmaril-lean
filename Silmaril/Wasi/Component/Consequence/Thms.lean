module

public import Silmaril.Wasi.Component.Consequence.Defs
public import Silmaril.Logic.Szs.Thms
import Silmaril.Proofs.Wasi.Component.Consequence.Basic

/-! # Components as consequence checkers: theorems

* **Witnesses**: an accepted query has a play witness, and `Nonempty` of the witness type is the
  Prop relation (`nonempty_acceptWitness_iff`).
* **Acceptance is SAT, not THM** (`accepted_iff_sat`). The execution status is classified
  (`classify_holds`, `classify_cases`), and accepted queries are exactly those classified `STH` or
  `NOC` (`accepted_iff_classify`).
* **Honest empty models**: when no query completes the status is `CAX` and `THM` holds vacuously
  (`thm_of_cax`, `execProblem_cax_iff`), without acceptance (`exists_thm_not_accepted`); `THM`
  gives acceptance only with a completed query (`accepted_of_thm`). Current `STH` is the 2007
  `SAT ∧ THM` (`sth_iff_v2007`; the 2007 text has no `STH`).
* **No negative observations of import calls**: an import claim observed at `.call` never has a
  countermodel (`importAssert_call_thm`).
* **Hosts**: restricting the traces (to a host, an environment) shrinks acceptance
  (`accepted_mono`, `existsHost_accepted`); every host gives some host only over a nonempty class
  (`forallHosts_existsHost`; `forallHosts_empty` is vacuous).
* **Epochs**: the state after a reset depends only on the steps after it
  (`epochState_append_reset`).
* **Bridges under structural closure of the target**: policy morphisms map states
  (`hom_epochState`) and accepted queries (`accepted_stateful_hom`); soundness transports along a
  morphism when the target is invariant on its fibres (`sound_hom`), e.g. from lists to finite
  sets when the target is closed under exchange, contraction and duplication
  (`finset_sound_of_mem_closed`), and to permuted assumptions when it is closed under permutation
  (`sound_perm_closure`). None of these says a component has the closure property.

Proofs: `Silmaril.Proofs.Wasi.Component.Consequence.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Logic Silmaril.Logic.Szs
open Silmaril.Wasm.Component (Val)

universe u v u₁ u₂ u₃

variable {X : Type u} {C : Type v} {A : Type u₁} {S : Type u₂} {S' : Type u₃}
  {T T' : Set (List WEv)} {r : Reading X C} {x : X} {c : C}

/-! ## Witnesses and answers -/

/-- **An accepted query has a witness, and the witness type erases to acceptance.** -/
theorem nonempty_acceptWitness_iff : Nonempty (AcceptWitness T r x c) ↔ Accepted T r x c :=
  ⟨fun ⟨⟨p, h⟩⟩ => ⟨p.1, p.2, h⟩, fun ⟨s, e, h⟩ => ⟨⟨(s, e), h⟩⟩⟩

theorem accepted_iff_answered : Accepted T r x c ↔ Answered T r x c .yes := Iff.rfl

theorem accepted_mono (h : T ⊆ T') (ha : Accepted T r x c) : Accepted T' r x c :=
  let ⟨s, e, hT, hr⟩ := ha; ⟨s, e, h hT, hr⟩

@[simp] theorem Answer.ofResult_true : Answer.ofResult (some [.bool true]) = .yes := rfl
@[simp] theorem Answer.ofResult_false : Answer.ofResult (some [.bool false]) = .no := rfl
@[simp] theorem Answer.ofResult_none : Answer.ofResult none = .trap := rfl

/-! ## Execution status -/

/-- **Existential acceptance is the SAT status of the execution model.** -/
theorem accepted_iff_sat : Accepted T r x c ↔ Current.SAT (execProblem T r x c) :=
  Proofs.Wasi.Component.Consequence.accepted_iff_sat

/-- **The classified status holds** (current ontology). -/
theorem classify_holds {I : Type} (P : Problem I) : (classify P).holds P :=
  Proofs.Wasi.Component.Consequence.classify_holds P

theorem classify_cases {I : Type} (P : Problem I) :
    classify P = .CAX ∨ classify P = .STH ∨ classify P = .SCT ∨ classify P = .NOC :=
  Proofs.Wasi.Component.Consequence.classify_cases P

theorem classify_eq_cax_iff {I : Type} (P : Problem I) : classify P = .CAX ↔ Current.CAX P :=
  Proofs.Wasi.Component.Consequence.classify_eq_cax_iff P

/-- **Accepted queries are those classified `STH` or `NOC`.** -/
theorem accepted_iff_classify :
    Accepted T r x c ↔ (status T r x c).exec = .STH ∨ (status T r x c).exec = .NOC :=
  accepted_iff_sat.trans (Proofs.Wasi.Component.Consequence.sat_iff_classify _)

theorem status_consequence : (status T r x c).consequence ↔ Accepted T r x c := Iff.rfl

/-- `CAX`: no query `(x, c)` completes. -/
theorem execProblem_cax_iff :
    Current.CAX (execProblem T r x c) ↔ ∀ a, ¬ Answered T r x c a :=
  Proofs.Wasi.Component.Consequence.execProblem_cax_iff

/-- `THM`: every completed query `(x, c)` answers `yes`. -/
theorem execProblem_thm_iff :
    Current.THM (execProblem T r x c) ↔ ∀ a, Answered T r x c a → a = .yes :=
  Proofs.Wasi.Component.Consequence.execProblem_thm_iff

/-- `CSA`: some completed query `(x, c)` answers `no`, traps or answers otherwise. -/
theorem execProblem_csa_iff :
    Current.CSA (execProblem T r x c) ↔ ∃ a, a ≠ .yes ∧ Answered T r x c a :=
  Proofs.Wasi.Component.Consequence.execProblem_csa_iff

/-- **With no models of the axioms, `THM` holds vacuously.** -/
theorem thm_of_cax {I : Type} {P : Problem I} (h : Current.CAX P) : Current.THM P := by
  simp only [Current.CAX] at h; simp [Current.THM, h]

/-- **`THM` without acceptance**: the empty trace model. -/
theorem exists_thm_not_accepted :
    ∃ (T : Set (List WEv)) (r : Reading Unit Unit),
      Current.THM (execProblem T r () ()) ∧ ¬ Accepted T r () () :=
  Proofs.Wasi.Component.Consequence.exists_thm_not_accepted

/-- **`THM` with a completed query gives acceptance.** -/
theorem accepted_of_thm (hne : (execProblem T r x c).ax.Nonempty)
    (h : Current.THM (execProblem T r x c)) : Accepted T r x c :=
  Proofs.Wasi.Component.Consequence.accepted_of_thm hne h

/-- Current `STH` is the 2007 `SAT ∧ THM`. -/
theorem sth_iff_v2007 {I : Type} {P : Problem I} : Current.STH P ↔ V2007.SAT P ∧ V2007.THM P :=
  ⟨fun ⟨⟨i, hi⟩, h⟩ => ⟨⟨⟨i, hi⟩, i, hi, h hi⟩, h⟩,
    fun ⟨⟨hne, _⟩, h⟩ => ⟨hne, h⟩⟩

/-- **An import claim observed at its call has no countermodel.** -/
theorem importAssert_call_thm {f : FnName} {dec : List Val → Option (X × C)} :
    Current.THM (execProblem T (importAssert .call f dec) x c) :=
  Proofs.Wasi.Component.Consequence.importAssert_call_thm

/-! ## Hosts -/

theorem existsHost_accepted {H : Set HostFn} (h : ExistsHost H T r x c) : Accepted T r x c :=
  let ⟨_, _, ha⟩ := h; accepted_mono Set.inter_subset_left ha

/-- **Every host to some host needs a host**: over a nonempty class. -/
theorem forallHosts_existsHost {H : Set HostFn} (hH : H.Nonempty) (h : ForallHosts H T r x c) :
    ExistsHost H T r x c :=
  Proofs.Wasi.Component.Consequence.forallHosts_existsHost hH h

/-- Over the empty class of hosts, `ForallHosts` holds of everything. -/
theorem forallHosts_empty : ForallHosts ∅ T r x c := fun _ h => h.elim

/-! ## Epochs and policies -/

/-- **A reset forgets the earlier epoch.** -/
theorem epochState_append_reset (P : Policy A S) (l l' : List (Step A)) :
    epochState P (l ++ .reset :: l') = epochState P l' :=
  Proofs.Wasi.Component.Consequence.epochState_append_reset P l l'

theorem hom_epochState {P : Policy A S} {Q : Policy A S'} (h : P.Hom Q) (l : List (Step A)) :
    h.toFun (epochState P l) = epochState Q l :=
  Proofs.Wasi.Component.Consequence.hom_epochState h l

/-- **Accepted queries along a policy morphism**: the states are the images. -/
theorem accepted_stateful_hom {P : Policy A S} {Q : Policy A S'} (h : P.Hom Q)
    {stepOf : WEv → Option (Step A)} {claim : WEv → Option (C × Answer)} {y : S'} :
    Accepted T (stateful Q stepOf claim) y c ↔
      ∃ x, h.toFun x = y ∧ Accepted T (stateful P stepOf claim) x c :=
  Proofs.Wasi.Component.Consequence.accepted_stateful_hom h

/-- **Soundness transports along a morphism whose fibres the target cannot tell apart.** -/
theorem sound_hom {P : Policy A S} {Q : Policy A S'} (h : P.Hom Q)
    {stepOf : WEv → Option (Step A)} {claim : WEv → Option (C × Answer)}
    {target : S → C → Prop} (hs : Sound (Accepted T (stateful P stepOf claim)) target)
    (hinv : ∀ x x' c, h.toFun x = h.toFun x' → target x c → target x' c) :
    Sound (Accepted T (stateful Q stepOf claim)) fun y c => ∀ x, h.toFun x = y → target x c :=
  Proofs.Wasi.Component.Consequence.sound_hom h hs hinv

/-- **Lists to finite sets, under closure of the target** under exchange, contraction and
duplication (the target sees only which assumptions occur). -/
theorem finset_sound_of_mem_closed [DecidableEq A] {stepOf : WEv → Option (Step A)}
    {claim : WEv → Option (C × Answer)} {target : List A → C → Prop}
    (hs : Sound (Accepted T (stateful Policy.list stepOf claim)) target)
    (hclosed : ∀ xs ys c, (∀ a, a ∈ xs ↔ a ∈ ys) → target xs c → target ys c) :
    Sound (Accepted T (stateful Policy.finset stepOf claim))
      fun s c => ∀ xs : List A, xs.toFinset = s → target xs c :=
  Proofs.Wasi.Component.Consequence.finset_sound_of_mem_closed hs hclosed

/-- **Permuting assumptions, under closure of the target under permutation.** -/
theorem sound_perm_closure {R target : List A → C → Prop} (hs : Sound R target)
    (hperm : ∀ xs ys c, xs.Perm ys → target xs c → target ys c) :
    Sound (fun ys c => ∃ xs, xs.Perm ys ∧ R xs c) target :=
  Proofs.Wasi.Component.Consequence.sound_perm_closure hs hperm

end Silmaril.Wasi.Consequence
