module

public import Silmaril.Wasm.Game.Accept.Reject.Defs
public import Silmaril.Wasm.Game.Accept.Thms
public import Silmaril.Semantics.Accept.Rel.Thms

/-! # Rejection, never-rejection and indexed callouts of modules: theorems

* `neverRejected` is `Silmaril.Accept.neverRejects` of the rejecting callouts
  (`neverRejected_eq`). Its complement is `rejected` (`compl_neverRejected`).
* Never-rejection is **antitone** in the environments: admitting more environments can only
  add rejections (`neverRejected_anti`), while acceptance grows (`accepted_mono`).
* Callout-equivalent modules have the same never-rejected sets
  (`neverRejected_eq_of_calloutEquiv`). Indexed sets need the finer equality of indexed calls
  (`indexed_eq_of_calls_eq`): callout equivalence forgets which import index was called.
* The callouts are the indexed calls with the index forgotten (`callouts_eq_image_calls`).
  So acceptance through `imp` is the union over the indices whose import is named `imp`
  (`accepted_eq_iUnion_indexed`), and erasing all indices accepts through any import
  (`eraseSome_indexed`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Formats.Accept

variable {α : Type} {dec : Callout → Option α} {P : Profile}
  {Envs Envs' : Store Nat → SEnv UImp → Prop} {k : Nat} {rej imp : String × String}
  {m m' : Module}

theorem mem_neverRejected {a : α} :
    a ∈ neverRejected dec P Envs k rej m ↔
      ∀ o ∈ Callouts P Envs k m, o.imp = rej → dec o ≠ some a := by
  simp only [neverRejected, rejected, Set.mem_compl_iff, mem_accepted, not_exists, not_and]

theorem compl_neverRejected :
    (neverRejected dec P Envs k rej m)ᶜ = rejected dec P Envs k rej m := compl_compl _

/-- **Never-rejection is `Silmaril.Accept.neverRejects`** of the rejecting callouts. -/
theorem neverRejected_eq :
    neverRejected dec P Envs k rej m =
      Silmaril.Accept.neverRejects (rejectRuns dec P Envs k rej m) Set.univ := by
  ext a
  simp only [Silmaril.Accept.mem_neverRejects, Set.mem_univ, not_true_eq_false, imp_false]
  constructor
  · rintro h o ⟨ho, hi, hd⟩; exact h ⟨o, ho, hi, hd⟩
  · rintro h ⟨o, ho, hi, hd⟩; exact h o ⟨ho, hi, hd⟩

/-- More admitted environments, fewer never-rejected values. -/
theorem neverRejected_anti (h : ∀ s L, Envs s L → Envs' s L) :
    neverRejected dec P Envs' k rej m ⊆ neverRejected dec P Envs k rej m :=
  Set.compl_subset_compl.2 (accepted_mono h dec rej)

theorem neverRejected_eq_of_calloutEquiv (h : CalloutEquiv P Envs k m m') :
    neverRejected dec P Envs k rej m = neverRejected dec P Envs k rej m' := by
  unfold neverRejected rejected; rw [accepted_eq_of_calloutEquiv h]

theorem acceptedNotRejected_eq_of_calloutEquiv (h : CalloutEquiv P Envs k m m') :
    acceptedNotRejected dec P Envs k imp rej m = acceptedNotRejected dec P Envs k imp rej m' := by
  unfold acceptedNotRejected
  rw [accepted_eq_of_calloutEquiv h, neverRejected_eq_of_calloutEquiv h]

/-- When the accepting and rejecting imports coincide, nothing is accepted and never
rejected. -/
theorem acceptedNotRejected_self : acceptedNotRejected dec P Envs k imp imp m = ∅ :=
  Set.inter_compl_self _

/-! ## Indexed callouts -/

theorem calloutOf_iff {memAddr : Option Nat} {c : Config Nat} {o : Callout} :
    CalloutOf m memAddr c o ↔ ∃ h, CalloutAtIdx m memAddr c h o :=
  ⟨fun ⟨E, fa, h, hd, hi, hm⟩ => ⟨h, E, fa, hd, hi, hm⟩,
    fun ⟨h, E, fa, hd, hi, hm⟩ => ⟨E, fa, h, hd, hi, hm⟩⟩

/-- **The callouts are the indexed calls, index forgotten.** -/
theorem callouts_eq_image_calls : Callouts P Envs k m = Prod.snd '' Calls P Envs k m := by
  ext o
  constructor
  · rintro ⟨mt, I, c₀, hI, L, q₀, hL, b, c, q, hs, hc⟩
    obtain ⟨h, hh⟩ := calloutOf_iff.1 hc
    exact ⟨(h, o), ⟨mt, I, c₀, hI, L, q₀, hL, b, c, q, hs, hh⟩, rfl⟩
  · rintro ⟨⟨h, o⟩, ⟨mt, I, c₀, hI, L, q₀, hL, b, c, q, hs, hh⟩, rfl⟩
    exact ⟨mt, I, c₀, hI, L, q₀, hL, b, c, q, hs, calloutOf_iff.2 ⟨h, hh⟩⟩

/-- An indexed call names the import at its index. -/
theorem imp_of_mem_calls {i : Nat} {o : Callout} (h : (i, o) ∈ Calls P Envs k m) :
    (m.imports[i]?).map (fun x => (x.moduleName, x.name)) = some o.imp :=
  h.elim fun _ ⟨_, _, _, _, _, _, _, _, _, _, hc⟩ => hc.elim fun _ ⟨_, _, hi, _⟩ => hi

/-- Erasing the index: the values accepted through some import. -/
theorem eraseSome_indexed :
    Silmaril.Accept.eraseSome (indexed dec P Envs k m) =
      {a | ∃ o ∈ Callouts P Envs k m, dec o = some a} := by
  ext a
  simp only [Silmaril.Accept.eraseSome, Set.mem_iUnion, indexed, Set.mem_ofPred_eq,
    callouts_eq_image_calls, Set.mem_image, Prod.exists]
  constructor
  · rintro ⟨i, o, ho, hd⟩; exact ⟨o, ⟨i, o, ho, rfl⟩, hd⟩
  · rintro ⟨o, ⟨i, _, ho, rfl⟩, hd⟩; exact ⟨i, _, ho, hd⟩

/-- **Acceptance through `imp` is the union of the indexed values over the indices whose
import is named `imp`.** -/
theorem accepted_eq_iUnion_indexed :
    accepted dec P Envs k imp m =
      ⋃ (i : Nat) (_ : (m.imports[i]?).map (fun x => (x.moduleName, x.name)) = some imp),
        indexed dec P Envs k m i := by
  ext a
  simp only [mem_accepted, callouts_eq_image_calls, Set.mem_image, Prod.exists,
    Set.mem_iUnion, indexed, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨o, ⟨i, _, ho, rfl⟩, rfl, hd⟩
    exact ⟨i, imp_of_mem_calls ho, _, ho, hd⟩
  · rintro ⟨i, hi, o, ho, hd⟩
    refine ⟨o, ⟨i, o, ho, rfl⟩, ?_, hd⟩
    have := imp_of_mem_calls ho
    rw [hi] at this
    exact (Option.some.inj this).symm

/-- Modules with the same indexed calls have the same indexed sets. -/
theorem indexed_eq_of_calls_eq (h : Calls P Envs k m = Calls P Envs k m') :
    indexed dec P Envs k m = indexed dec P Envs k m' := by
  unfold indexed; rw [h]

/-- Equal indexed calls give callout equivalence. -/
theorem calloutEquiv_of_calls_eq (h : Calls P Envs k m = Calls P Envs k m') :
    CalloutEquiv P Envs k m m' := by
  unfold CalloutEquiv; rw [callouts_eq_image_calls, callouts_eq_image_calls, h]

theorem calls_mono (h : ∀ s L, Envs s L → Envs' s L) : Calls P Envs k m ⊆ Calls P Envs' k m :=
  fun _ ⟨mt, I, c₀, hI, L, q₀, hL, rest⟩ => ⟨mt, I, c₀, hI, L, q₀, h _ _ hL, rest⟩

end Silmaril.Wasm.Game.Accept
