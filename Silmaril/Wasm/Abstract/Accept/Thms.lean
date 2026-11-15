module

public import Silmaril.Wasm.Abstract.Accept.Defs
public import Silmaril.Games.Abstract.Machine.Thms
public import Silmaril.Games.Abstract.Game.Thms
public import Silmaril.Games.Accept.Thms
public import Silmaril.Semantics.Accept.Verdict.Thms

/-! # Acceptor sets of abstract modules and components: theorems

* **Verdicts are observations**: `tmAcceptsSome T val acc` is `tmAccepted` of the observation
  restricted to `acc` (`tmAcceptsSome_eq`); `tmNeverRejects` is the complement of the rejecting
  observation (`tmNeverRejects_eq`).
* **Order and equivalence**: a larger trace model accepts more and never-rejects less
  (`tmAccepted_mono`, `tmNeverRejects_anti`); equal or bisimilar machines accept the same
  (`mAccepted_eq_of_bisim`). The combined verdict is **not** monotone (the generic
  `Silmaril.Accept.not_mono_runner`, `not_anti_runner`).
* **Machines and their denotations agree on Proponent observations**: `denote M` adds only
  Opponent moves to the legal traces, so an observation of Proponent moves reads the same
  values (`tmAccepted_denote`). The same holds for the runner (`tmRun_denote`) and hence every
  verdict (`tmAcceptsSafely_denote`, …).
* **Runners along maps**: verdicts of an image runner are verdicts of the runner on the
  preimages (`acceptsSome_image`, `neverRejects_image`, `acceptsSafely_image`); this transports
  verdicts along observation-preserving maps (event views, behaviour projections).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.Accept

open Silmaril.Games Silmaril.Games.Abstract

universe u v w

/-! ## Runners along maps -/

section Image

variable {α : Type u} {ω : Type v} {ω' : Type w}

theorem acceptsSome_image (run : α → Set ω) (f : ω → ω') (acc : Set ω') :
    Silmaril.Accept.acceptsSome (fun a => f '' run a) acc =
      Silmaril.Accept.acceptsSome run (f ⁻¹' acc) := by
  ext a
  simp only [Silmaril.Accept.mem_acceptsSome, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, h⟩; exact ⟨o, ho, h⟩
  · rintro ⟨o, ho, h⟩; exact ⟨_, ⟨o, ho, rfl⟩, h⟩

theorem neverRejects_image (run : α → Set ω) (f : ω → ω') (rej : Set ω') :
    Silmaril.Accept.neverRejects (fun a => f '' run a) rej =
      Silmaril.Accept.neverRejects run (f ⁻¹' rej) := by
  ext a
  simp only [Silmaril.Accept.mem_neverRejects, Set.mem_image, Set.mem_preimage]
  constructor
  · intro h o ho hr; exact h _ ⟨o, ho, rfl⟩ hr
  · rintro h _ ⟨o, ho, rfl⟩ hr; exact h o ho hr

theorem acceptsSafely_image (run : α → Set ω) (f : ω → ω') (acc rej : Set ω') :
    Silmaril.Accept.acceptsSafely (fun a => f '' run a) acc rej =
      Silmaril.Accept.acceptsSafely run (f ⁻¹' acc) (f ⁻¹' rej) := by
  unfold Silmaril.Accept.acceptsSafely
  rw [acceptsSome_image, neverRejects_image]

/-- Equal runners give equal verdicts (stated for rewriting under binders). -/
theorem acceptsSafely_congr {run run' : α → Set ω} (h : ∀ a, run a = run' a) (acc rej : Set ω) :
    Silmaril.Accept.acceptsSafely run acc rej = Silmaril.Accept.acceptsSafely run' acc rej := by
  rw [show run = run' from funext h]

end Image

/-! ## Trace models -/

section TraceModels

variable {G : Game.{u}} {α : Type v} {T U : TraceModel G} {obs val : G.Move → Option α}

theorem mem_tmAccepted {a : α} : a ∈ tmAccepted T obs ↔ ∃ s ∈ T.plays, ∃ m ∈ s, obs m = some a :=
  Iff.rfl

theorem tmAccepted_mono (h : T ≤ U) : tmAccepted T obs ⊆ tmAccepted U obs :=
  Silmaril.Games.Accept.observed_mono fun _ hs => h hs

theorem tmRun_mono (h : T ≤ U) (a : α) : tmRun T val a ⊆ tmRun U val a :=
  fun _ ⟨⟨s, hs, hm⟩, hv⟩ => ⟨⟨s, h hs, hm⟩, hv⟩

theorem tmAcceptsSome_mono (h : T ≤ U) (acc : Set G.Move) :
    tmAcceptsSome T val acc ⊆ tmAcceptsSome U val acc :=
  Silmaril.Accept.acceptsSome_of_le fun a => tmRun_mono h a

theorem tmNeverRejects_anti (h : T ≤ U) (rej : Set G.Move) :
    tmNeverRejects U val rej ⊆ tmNeverRejects T val rej := by
  show Silmaril.Accept.acceptsAll _ rejᶜ ⊆ Silmaril.Accept.acceptsAll _ rejᶜ
  exact Silmaril.Accept.acceptsAll_of_le fun a => tmRun_mono h a

/-- **Some-accepts is the restricted observation.** -/
theorem tmAcceptsSome_eq (acc : Set G.Move) [DecidablePred (· ∈ acc)] :
    tmAcceptsSome T val acc = tmAccepted T (restrictObs val acc) := by
  ext a
  simp only [tmAcceptsSome, Silmaril.Accept.mem_acceptsSome, tmRun, Set.mem_ofPred_eq,
    mem_tmAccepted, restrictObs]
  constructor
  · rintro ⟨m, ⟨⟨s, hs, hm⟩, hv⟩, hacc⟩; exact ⟨s, hs, m, hm, by simp [hacc, hv]⟩
  · rintro ⟨s, hs, m, hm, h⟩
    by_cases hacc : m ∈ acc
    · simp only [hacc, ite_true] at h; exact ⟨m, ⟨⟨s, hs, hm⟩, h⟩, hacc⟩
    · simp [hacc] at h

/-- **Never-rejects is the complement of the rejecting observation.** -/
theorem tmNeverRejects_eq (rej : Set G.Move) [DecidablePred (· ∈ rej)] :
    tmNeverRejects T val rej = (tmAccepted T (restrictObs val rej))ᶜ := by
  rw [← tmAcceptsSome_eq]
  exact Silmaril.Accept.compl_rejectsSome.symm

end TraceModels

/-! ## Machines and their denotations -/

section Machines

variable {G : Game.{u}} {α : Type v} {M N : Machine G} {obs val : G.Move → Option α}

/-- Plays of the denotation: a legal trace prefix followed by Opponent moves. -/
theorem mem_denote_iff {p : List G.Move} :
    p ∈ M.denote ↔ p ∈ G.Legal ∧ ∃ s, (s = [] ∨ (s ∈ M.traces ∧ s ∈ G.Legal)) ∧
      ∃ p₀ w, p = p₀ ++ w ∧ p₀ <+: s ∧ ∀ o ∈ w, G.IsO o := Iff.rfl

/-- A move of a play of the denotation that is not an Opponent move lies in a legal trace. -/
theorem exists_trace_of_mem_denote {p : List G.Move} (hp : p ∈ M.denote) {m : G.Move}
    (hm : m ∈ p) (hP : ¬ G.IsO m) : ∃ s ∈ M.traces ∩ G.Legal, m ∈ s := by
  obtain ⟨-, s, hs, p₀, w, rfl, hp₀, hw⟩ := mem_denote_iff.1 hp
  rcases List.mem_append.1 hm with hm | hm
  · rcases hs with rfl | ⟨hs, hl⟩
    · exact absurd (hp₀.subset hm) (by simp)
    · exact ⟨s, ⟨hs, hl⟩, hp₀.subset hm⟩
  · exact absurd (hw m hm) hP

/-- **On Proponent observations, a machine and its denotation accept the same.** -/
theorem tmAccepted_denote (hP : ∀ m a, obs m = some a → ¬ G.IsO m) :
    tmAccepted M.denote obs = mAccepted M obs := by
  ext a
  constructor
  · rintro ⟨p, hp, m, hm, ho⟩
    obtain ⟨s, hs, hms⟩ := exists_trace_of_mem_denote hp hm (hP m a ho)
    exact ⟨s, hs, m, hms, ho⟩
  · rintro ⟨s, ⟨hs, hl⟩, m, hm, ho⟩
    exact ⟨s, Machine.mem_denote_of_mem_traces hs hl, m, hm, ho⟩

/-- The runner of the denotation is the runner of the legal traces, on Proponent moves. -/
theorem tmRun_denote (hP : ∀ m a, val m = some a → ¬ G.IsO m) (a : α) :
    tmRun M.denote val a = {m | (∃ s ∈ M.traces ∩ G.Legal, m ∈ s) ∧ val m = some a} := by
  ext m
  constructor
  · rintro ⟨⟨p, hp, hm⟩, hv⟩
    exact ⟨exists_trace_of_mem_denote hp hm (hP m a hv), hv⟩
  · rintro ⟨⟨s, ⟨hs, hl⟩, hm⟩, hv⟩
    exact ⟨⟨s, Machine.mem_denote_of_mem_traces hs hl, hm⟩, hv⟩

/-- Bisimilar machines accept the same. -/
theorem mAccepted_eq_of_bisim (h : M.Bisim N) : mAccepted M obs = mAccepted N obs := by
  unfold mAccepted; rw [Machine.traces_eq_of_bisim h]

theorem tmAccepted_denote_eq_of_bisim (h : M.Bisim N) :
    tmAccepted M.denote obs = tmAccepted N.denote obs := by
  rw [Machine.denote_eq_of_bisim h]

end Machines

/-! ## Abstract functions -/

section Functions

variable {E : Sig.{u}} {S A B : Type u} {α : Type u}

theorem mem_endRun {f : AFun E S A B} {D : Set S} {a : A} {e : End S B} :
    e ∈ endRun f D a ↔ ∃ s ∈ D, ∃ x ∈ f s a, x.2 = e := Iff.rfl

/-- More admitted states, more endings. -/
theorem endRun_mono {f : AFun E S A B} {D D' : Set S} (h : D ⊆ D') (a : A) :
    endRun f D a ⊆ endRun f D' a :=
  fun _ ⟨s, hs, rest⟩ => ⟨s, h hs, rest⟩

/-- A refining function (fewer behaviours) has fewer endings. -/
theorem endRun_le {f g : AFun E S A B} (h : ∀ s a, f s a ⊆ g s a) (D : Set S) (a : A) :
    endRun f D a ⊆ endRun g D a :=
  fun _ ⟨s, hs, x, hx, he⟩ => ⟨s, hs, x, h s a hx, he⟩

/-- Observationally equivalent functions (under the ending observation) have the same
endings. -/
theorem endRun_eq_of_obsEquiv {f g : AFun E S A B} (h : AFun.ObsEquiv AFun.obsIO f g) (D : Set S) (a : A) :
    endRun f D a = endRun g D a := by
  ext e
  constructor
  · rintro ⟨s, hs, x, hx, rfl⟩
    have : x.2 ∈ AFun.obsIO '' g s a := h s a ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := this
    exact ⟨s, hs, y, hy, he⟩
  · rintro ⟨s, hs, x, hx, rfl⟩
    have : x.2 ∈ AFun.obsIO '' f s a := (h s a).symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := this
    exact ⟨s, hs, y, hy, he⟩

theorem retAcceptsSafely_eq_of_obsEquiv {f g : AFun E S A B} (h : AFun.ObsEquiv AFun.obsIO f g)
    (D : Set S) (acc rej : Set (End S B)) :
    retAcceptsSafely f D acc rej = retAcceptsSafely g D acc rej :=
  acceptsSafely_congr (endRun_eq_of_obsEquiv h D) acc rej

/-- The relational form projects to the import reading. -/
theorem callAccepted_eq_range (f : AFun E S A B) (D : Set S) (obs : Call E → Option α) :
    callAccepted f (D ×ˢ Set.univ) obs = Prod.snd '' callRel f D obs := by
  ext v
  constructor
  · rintro ⟨⟨s, a⟩, ⟨hs, -⟩, x, hx, c, hc, ho⟩
    exact ⟨(a, v), ⟨s, hs, x, hx, c, hc, ho⟩, rfl⟩
  · rintro ⟨⟨a, _⟩, ⟨s, hs, x, hx, c, hc, ho⟩, rfl⟩
    exact ⟨(s, a), ⟨hs, trivial⟩, x, hx, c, hc, ho⟩

end Functions

end Silmaril.Wasm.Abstract.Accept
