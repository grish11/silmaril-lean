module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Defs
public import Silmaril.Semantics.Accept.Handle.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic

/-! # Proofs: reader languages under non-trapping read policies

* `rrun_facts`: along a run of the reader host under a read policy other than `ub` (and an
  accept policy other than `ub`), every read is an allowed answer and every accepted tree is
  the meaning of an accepted handle.
* `polLang_subset_of_AG`: the assume/guarantee bridge with `polISpec` (answers allowed by the
  policy), generalizing `Silmaril.Wasm.Game.HandleAccept.readerLang_subset_of_AG` from the
  trapping policy to `dflt` and `arbitrary`.
* `errD_disjoint`: the error answers are a typed error for the cons reader.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.ReadPolicy Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Host Silmaril.Proofs.Wasm.Game.HandleAccept Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood)

variable {Q A H X : Type} {R : Reader Q A H X} {pol : OnBadRead Q A} {oa : OnInvalid}
  {ρ : Env H X}

theorem answers_isSome (hp : pol ≠ .ub) (q : Q) : ∃ S, answers R pol ρ q = some S := by
  unfold answers
  split
  · exact ⟨_, rfl⟩
  · cases pol
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact absurd rfl hp

theorem rrun_facts (hp : pol ≠ .ub) (hoa : oa ≠ .ub) :
    ∀ {p p' : Phase} {t : List (REv Q A H)} {S : Set X}, (reader R pol oa ρ).Run p t p' S →
      p ≠ .chaos →
      (∀ q a, REv.read q a ∈ t → ∃ S', answers R pol ρ q = some S' ∧ a ∈ S') ∧
      ∀ x ∈ S, ∃ h, REv.accept h ∈ t ∧ ρ h = some x := by
  intro p p' t S hr
  induction hr with
  | nil => exact fun _ => ⟨by simp, by simp⟩
  | @cons p p₁ p₂ e es S₁ S₂ hs _ ih =>
    intro hpc
    have step : p₁ ≠ .chaos ∧
        (∀ q a, e = .read q a → ∃ S', answers R pol ρ q = some S' ∧ a ∈ S') ∧
        ∀ x ∈ S₁, ∃ h, e = .accept h ∧ ρ h = some x := by
      cases hs with
      | read hS ha => exact ⟨by simp, fun q a he => by cases he; exact ⟨_, hS, ha⟩, by simp⟩
      | @readChaos q a hn =>
          obtain ⟨S, hS⟩ := answers_isSome (R := R) (ρ := ρ) hp q
          rw [hS] at hn; cases hn
      | @acceptOk h t hh =>
          exact ⟨by simp, by simp, fun x hx => by
            simp only [Set.mem_singleton_iff] at hx; subst hx; exact ⟨h, rfl, hh⟩⟩
      | acceptCallTrap => exact ⟨by simp, by simp, by simp⟩
      | acceptSessionTrap => exact ⟨by simp, by simp, by simp⟩
      | acceptIgnore => exact ⟨by simp, by simp, by simp⟩
      | acceptChaos _ h => exact absurd h hoa
      | enter => exact ⟨by simp, by simp, by simp⟩
      | resume => exact ⟨by simp, by simp, by simp⟩
      | chaos => exact absurd rfl hpc
    obtain ⟨hp₁, hrd, hacc⟩ := step
    obtain ⟨hrd', hacc'⟩ := ih hp₁
    refine ⟨fun q a hm => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hm with he | hm
      · exact hrd q a he.symm
      · exact hrd' q a hm
    · rcases hx with hx | hx
      · obtain ⟨h, he, hh⟩ := hacc x hx
        exact ⟨h, by simp [he], hh⟩
      · obtain ⟨h, hm, hh⟩ := hacc' x hx
        exact ⟨h, List.mem_cons_of_mem _ hm, hh⟩

variable {E F : Sig.{0}}

/-- **The policy bridge**: plays assume/guarantee correct for `polISpec R pol … ρ L` have their
reader language in `ρ` under `pol` included in `L`, for every read policy and accept policy
other than `ub`. -/
theorem polLang_subset_of_AG {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (REv Q A H)} {dAns : (e : E.Op) → E.Ar e → Option (REv Q A H)}
    (hAG : ∀ p ∈ σ, AG (polISpec R pol dAsk dAns ρ L) (topISpec F) p)
    (hans : ∀ e v h, dAns e v ≠ some (.accept h)) (hp : pol ≠ .ub) (hoa : oa ≠ .ub) :
    readerLang R pol oa {ρ} (handleTraces σ (some .enter) dAsk dAns) ⊆ L := by
  intro x hx
  unfold readerLang langOver at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨⟨ρ', hρ'⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff] at hρ'
  subst ρ'
  obtain ⟨t, ⟨p, hp', rfl⟩, ph, S, hr, hxS⟩ := mem_lang.1 hx
  obtain ⟨hrd, hacc⟩ := rrun_facts hp hoa hr (by simp [reader])
  have hgood : ∀ o ∈ p, Move.IsO o → MoveGood (polISpec R pol dAsk dAns ρ L) (topISpec F) o := by
    intro o ho hO
    rcases o with (e | ⟨e, v⟩) | (q | ⟨q, r⟩)
    · simp [Move.IsO] at hO
    · exact fun q a hd => hrd q a
        (ans_mem_playEvents (enter := some .enter) (decAsk := dAsk) ho hd)
    · trivial
    · simp [Move.IsO] at hO
  have hP := ag_allP (hAG p hp') hgood
  obtain ⟨h, hm, hh⟩ := hacc x hxS
  rcases mem_playEvents hm with ⟨e, he, hd⟩ | ⟨e, v, _, hd⟩ | hd
  · exact hP _ he trivial h hd x hh
  · exact absurd hd (hans e v h)
  · cases hd

/-! ## The error answers -/

theorem errD_disjoint : ErrorDisjoint (consR (BitVec 64) (BitVec 32)) errD := by
  intro ρ q a hok
  cases q <;> cases a <;> simp_all [consR, errD]

variable {ts : List FnType}

theorem errDecAns_ne_accept (ix : ConsImports) (e : (ifaceSig ts).Op)
    (v : (ifaceSig ts).Ar e) (h : BitVec 32) : errDecAns ix e v ≠ some (.accept h) := by
  intro hd
  unfold errDecAns at hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hd
  obtain ⟨_, -, _, -, hd⟩ := hd
  split_ifs at hd <;> simp only [Option.bind_eq_some_iff, Option.some.injEq] at hd <;>
    obtain ⟨_, -, hd⟩ := hd <;> cases hd

end Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy
