module

public import Silmaril.Wasm.Game.Accept.Acceptor.Thms
public import Silmaril.Semantics.Accept.Verdict.Thms

/-! # Modules: some run accepts and no run rejects

`acceptedNotRejected dec P Envs k acc rej m` (`Silmaril.Wasm.Game.Accept.Reject`) is an
instance of the generic `Silmaril.Accept.acceptsSafely` (#296) with **one** runner for both
quantifiers. The runner `moduleRun` sends a value to the reachable callouts carrying it,
for the same profile, the same environment class `Envs` and the same memory. Accepting
outcomes are calls of `acc`, rejecting outcomes calls of `rej`
(`acceptedNotRejected_eq_acceptsSafely`). So "some run accepts" and "no run rejects"
quantify over the same executions against the same hosts.

The generic laws then apply:

* no reachable callout carries the value: it is not accepted, though it is never rejected
  (`not_mem_acceptedNotRejected_of_no_callout`, `mem_neverRejected_of_no_callout`). This
  covers a value the module never passes to an import, including runs that diverge or trap
  first;
* a value both accepted and rejected, possibly on different runs, is excluded;
* one import for both verdicts gives the empty set (`acceptedNotRejected_self`, also
  `ModuleAcceptor.strictLang_self`): every accepting outcome rejects
  (`Silmaril.Accept.acceptsSafely_eq_empty_of_subset`);
* the set is invariant under callout equivalence (`acceptedNotRejected_eq_of_calloutEquiv`,
  in `Reject`).

It is **not** monotone in the environment class, in either direction. More environments can
add the accepting run, and they can also add a rejecting run; the generic
`Silmaril.Accept.not_mono_runner` and `not_anti_runner` exhibit both. The one-sided parts
are monotone: `accepted_mono` and `neverRejected_anti`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats.Accept

variable {α : Type} {dec : Callout → Option α} {P : Profile}
  {Envs : Store Nat → SEnv UImp → Prop} {k : Nat} {acc rej : String × String} {m : Module}

/-- The runner of a module: the reachable callouts carrying a value. -/
def moduleRun (dec : Callout → Option α) (P : Profile) (Envs : Store Nat → SEnv UImp → Prop)
    (k : Nat) (m : Module) (a : α) : Set Callout :=
  {o | o ∈ Callouts P Envs k m ∧ dec o = some a}

/-- The calls of the import `imp`. -/
def callsOf (imp : String × String) : Set Callout := {o | o.imp = imp}

/-- **Accepted and never rejected is `acceptsSafely` of one runner.** -/
theorem acceptedNotRejected_eq_acceptsSafely :
    acceptedNotRejected dec P Envs k acc rej m =
      Silmaril.Accept.acceptsSafely (moduleRun dec P Envs k m) (callsOf acc) (callsOf rej) := by
  ext a
  simp only [acceptedNotRejected, neverRejected, rejected, Set.mem_inter_iff,
    Set.mem_compl_iff, mem_accepted, Silmaril.Accept.acceptsSafely,
    Silmaril.Accept.mem_acceptsSome, Silmaril.Accept.mem_neverRejects, moduleRun, callsOf,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨o, ho, hi, hd⟩, hn⟩
    exact ⟨⟨o, ⟨ho, hd⟩, hi⟩, fun o' ⟨ho', hd'⟩ hi' => hn ⟨o', ho', hi', hd'⟩⟩
  · rintro ⟨⟨o, ⟨ho, hd⟩, hi⟩, hn⟩
    exact ⟨⟨o, ho, hi, hd⟩, fun ⟨o', ho', hi', hd'⟩ => hn o' ⟨ho', hd'⟩ hi'⟩

/-- **No reachable callout carries the value**: it is not accepted. -/
theorem not_mem_acceptedNotRejected_of_no_callout {a : α} (h : moduleRun dec P Envs k m a = ∅) :
    a ∉ acceptedNotRejected dec P Envs k acc rej m := by
  rw [acceptedNotRejected_eq_acceptsSafely]
  exact Silmaril.Accept.not_mem_acceptsSafely_of_eq_empty h

/-- ... but it is (vacuously) never rejected. -/
theorem mem_neverRejected_of_no_callout {a : α} (h : moduleRun dec P Envs k m a = ∅) :
    a ∈ neverRejected dec P Envs k rej m := by
  rintro ⟨o, ho, -, hd⟩
  have : o ∈ moduleRun dec P Envs k m a := ⟨ho, hd⟩
  rw [h] at this; exact this

/-- A value both accepted and rejected (on any runs) is excluded. -/
theorem not_mem_acceptedNotRejected_of_rejected {a : α}
    (h : a ∈ rejected dec P Envs k rej m) : a ∉ acceptedNotRejected dec P Envs k acc rej m :=
  fun hm => hm.2 h

namespace ModuleAcceptor

/-- With a reject import, the strict language is `acceptsSafely` of the module's runner. -/
theorem strictLang_eq_acceptsSafely (A : ModuleAcceptor) {r : String × String}
    (h : A.reject = some r) :
    A.strictLang = Silmaril.Accept.acceptsSafely
      (moduleRun (segmentDecoder A.addr) A.profile A.envs A.memIdx A.module)
      (callsOf A.accept) (callsOf r) := by
  rw [← acceptedNotRejected_eq_acceptsSafely]
  simp [strictLang, neverRejectedLang, h, lang, acceptedNotRejected]
  rfl

/-- An acceptor rejecting through its accepting import has an empty strict language. -/
theorem strictLang_self (A : ModuleAcceptor) (h : A.reject = some A.accept) :
    A.strictLang = ⊥ := by
  rw [A.strictLang_eq_acceptsSafely h]
  exact Silmaril.Accept.acceptsSafely_eq_empty_of_subset subset_rfl

end ModuleAcceptor

end Silmaril.Wasm.Game.Accept
