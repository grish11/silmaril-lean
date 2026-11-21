module

public import Silmaril.Wasm.Game.HandleAccept.Defs
public import Silmaril.Semantics.Accept.Handle.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms

/-! # Proofs: assume/guarantee plays give sound reader languages -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.HandleAccept
  Silmaril.Accept Silmaril.Accept.Handle
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood agStrat)

variable {E F : Sig.{0}} {Ev : Type}

/-- In an assume/guarantee play whose Opponent moves are all allowed, every Proponent move is
allowed. -/
theorem ag_allP {I : ISpec E} {S : ISpec F} :
    ∀ {p : List (Move E F)}, AG I S p → (∀ o ∈ p, Move.IsO o → MoveGood I S o) →
      ∀ o ∈ p, Move.IsP o → MoveGood I S o
  | [], _, _, o, ho, _ => by simp at ho
  | m :: p, ⟨hO, hP⟩, hall, o, ho, hp => by
      rcases Silmaril.Wasm.Logic.Strategy.Move.isO_or_isP m with hm | hm
      · have hg := hall m List.mem_cons_self hm
        rcases List.mem_cons.1 ho with rfl | ho
        · exact hg
        · exact ag_allP (hO hm hg) (fun o' h' => hall o' (List.mem_cons_of_mem _ h')) o ho hp
      · obtain ⟨hg, hrest⟩ := hP hm
        rcases List.mem_cons.1 ho with rfl | ho
        · exact hg
        · exact ag_allP hrest (fun o' h' => hall o' (List.mem_cons_of_mem _ h')) o ho hp

theorem mem_playEvents {enter : Option Ev} {decAsk : E.Op → Option Ev}
    {decAns : (e : E.Op) → E.Ar e → Option Ev} {ev : Ev} :
    ∀ {p : List (Move E F)}, ev ∈ playEvents enter decAsk decAns p →
      (∃ e, (.inl (.ask e) : Move E F) ∈ p ∧ decAsk e = some ev) ∨
      (∃ e v, (.inl (.ans e v) : Move E F) ∈ p ∧ decAns e v = some ev) ∨ enter = some ev
  | [], h => by simp [playEvents] at h
  | .inl (.ask e) :: p, h => by
      simp only [playEvents, List.mem_append, Option.mem_toList] at h
      rcases h with h | h
      · exact .inl ⟨e, List.mem_cons_self, h⟩
      · rcases mem_playEvents h with ⟨e', he, h'⟩ | ⟨e', v, he, h'⟩ | h'
        · exact .inl ⟨e', List.mem_cons_of_mem _ he, h'⟩
        · exact .inr (.inl ⟨e', v, List.mem_cons_of_mem _ he, h'⟩)
        · exact .inr (.inr h')
  | .inl (.ans e v) :: p, h => by
      simp only [playEvents, List.mem_append, Option.mem_toList] at h
      rcases h with h | h
      · exact .inr (.inl ⟨e, v, List.mem_cons_self, h⟩)
      · rcases mem_playEvents h with ⟨e', he, h'⟩ | ⟨e', v', he, h'⟩ | h'
        · exact .inl ⟨e', List.mem_cons_of_mem _ he, h'⟩
        · exact .inr (.inl ⟨e', v', List.mem_cons_of_mem _ he, h'⟩)
        · exact .inr (.inr h')
  | .inr (.ask _) :: p, h => by
      simp only [playEvents, List.mem_append, Option.mem_toList] at h
      rcases h with h | h
      · exact .inr (.inr h)
      · rcases mem_playEvents h with ⟨e', he, h'⟩ | ⟨e', v, he, h'⟩ | h'
        · exact .inl ⟨e', List.mem_cons_of_mem _ he, h'⟩
        · exact .inr (.inl ⟨e', v, List.mem_cons_of_mem _ he, h'⟩)
        · exact .inr (.inr h')
  | .inr (.ans _ _) :: p, h => by
      simp only [playEvents] at h
      rcases mem_playEvents h with ⟨e', he, h'⟩ | ⟨e', v, he, h'⟩ | h'
      · exact .inl ⟨e', List.mem_cons_of_mem _ he, h'⟩
      · exact .inr (.inl ⟨e', v, List.mem_cons_of_mem _ he, h'⟩)
      · exact .inr (.inr h')

theorem ans_mem_playEvents {enter : Option Ev} {decAsk : E.Op → Option Ev}
    {decAns : (e : E.Op) → E.Ar e → Option Ev} {e : E.Op} {v : E.Ar e} {ev : Ev} :
    ∀ {p : List (Move E F)}, (.inl (.ans e v) : Move E F) ∈ p → decAns e v = some ev →
      ev ∈ playEvents enter decAsk decAns p
  | [], h, _ => by simp at h
  | m :: p, h, hd => by
      rcases List.mem_cons.1 h with rfl | h
      · simp [playEvents, hd]
      · have := ans_mem_playEvents (enter := enter) (decAsk := decAsk) h hd
        rcases m with (e' | e') | (e' | e')
        · simp [playEvents, this]
        · simp [playEvents, this]
        · simp [playEvents, this]
        · simpa [playEvents] using this

theorem mem_reads {Q A H : Type} {q : Q} {a : A} :
    ∀ {t : List (REv Q A H)}, REv.read q a ∈ t → (q, a) ∈ REv.reads t
  | [], h => by simp at h
  | .read q' a' :: t, h => by
      simp only [REv.reads, List.mem_cons, Prod.mk.injEq]
      rcases List.mem_cons.1 h with h | h
      · cases h; exact .inl ⟨rfl, rfl⟩
      · exact .inr (mem_reads h)
  | .accept _ :: t, h => by
      simp only [REv.reads]
      rcases List.mem_cons.1 h with h | h
      · cases h
      · exact mem_reads h
  | .enter :: t, h => by
      simp only [REv.reads]
      rcases List.mem_cons.1 h with h | h
      · cases h
      · exact mem_reads h

/-- **The bridge**: if every play of `σ` is assume/guarantee correct for an import
specification whose answers are the correct reads in `ρ` and whose `accept` calls name members
of `L`, the reader language of `σ` in `ρ` (export calls decoded as `enter`) under the trapping
read policy is included in `L`, for every accept policy but `ub`. -/
theorem readerLang_subset_of_AG {Q A H X : Type} {R : Reader Q A H X} {ρ : Env H X} {L : Set X}
    {σ : Strategy E F} {decAsk : E.Op → Option (REv Q A H)}
    {decAns : (e : E.Op) → E.Ar e → Option (REv Q A H)} {Ii : ISpec E}
    (hAG : ∀ p ∈ σ, AG Ii (topISpec F) p)
    (hpost : ∀ e v, (∀ q a, decAns e v = some (.read q a) → R.valid ρ q ∧ R.ok ρ q a) →
      Ii.post e v)
    (hpre : ∀ e h, decAsk e = some (.accept h) → Ii.pre e → ∀ t, ρ h = some t → t ∈ L)
    (hans : ∀ e v h, decAns e v ≠ some (.accept h)) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    readerLang R .trap oa {ρ} (handleTraces σ (some .enter) decAsk decAns) ⊆ L := by
  intro x hx
  unfold readerLang langOver at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨⟨ρ', hρ'⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff] at hρ'
  subst ρ'
  obtain ⟨t, ⟨p, hp, rfl⟩, ph, S, hr, hxS⟩ := Host.mem_lang.1 hx
  have hreads := trap_reads_correct hoa hr
  have hgood : ∀ o ∈ p, Move.IsO o → MoveGood Ii (topISpec F) o := by
    intro o ho hO
    rcases o with (e | ⟨e, v⟩) | (q | ⟨q, r⟩)
    · simp [Move.IsO] at hO
    · exact hpost e v fun q a hd =>
        hreads (q, a)
          (mem_reads (ans_mem_playEvents (enter := some .enter) (decAsk := decAsk) ho hd))
    · trivial
    · simp [Move.IsO] at hO
  have hP := ag_allP (hAG p hp) hgood
  obtain ⟨u, ev, w, p₁, p₂, B, C, ht, hu, hev, hxC⟩ :=
    Host.Run.mem_split (h := reader R .trap oa ρ) (t := playEvents (some .enter) decAsk decAns p)
      hr hxS
  have hfacts := trap_reads_correct hoa hu
  cases hev with
  | read _ _ => simp at hxC
  | @readChaos q a hn =>
      by_cases hv : R.valid ρ q
      · simp [answers, hv] at hn
      · simp [answers, hv, badAnswers] at hn
  | @acceptOk h t' hρ =>
      simp only [Set.mem_singleton_iff] at hxC
      subst hxC
      have hmem : REv.accept h ∈ playEvents (some .enter) decAsk decAns p := by rw [ht]; simp
      rcases mem_playEvents hmem with ⟨e, he, hd⟩ | ⟨e, v, _, hd⟩ | hd
      · exact hpre e h hd (hP _ he trivial) _ hρ
      · exact absurd hd (hans e v h)
      · cases hd
  | acceptCallTrap _ _ => simp at hxC
  | acceptSessionTrap _ _ => simp at hxC
  | enter => simp at hxC
  | resume => simp at hxC
  | acceptIgnore _ _ => simp at hxC
  | acceptChaos _ h => exact absurd h hoa
  | chaos _ => exact absurd rfl (trap_not_chaos hoa hu)

/-! ## The cons reader decoder -/

/-- The answer decoder of the cons reader never decodes an `accept`. -/
theorem consDecAns_ne_accept {ts : List FnType} (ix : ConsImports) (e : (ifaceSig ts).Op)
    (v : (ifaceSig ts).Ar e) (h : BitVec 32) : consDecAns ix e v ≠ some (.accept h) := by
  intro hd
  unfold consDecAns at hd
  rcases h1 : i32Arg e.2.1 with _ | k <;> rcases h2 : ansVals v with _ | vs <;>
    simp only [h1, h2, Option.bind_eq_bind, Option.bind_none, Option.bind_some] at hd
  · cases hd
  · cases hd
  · cases hd
  · split_ifs at hd <;> revert hd <;> cases i32Res vs <;> cases i64Res vs <;> simp

end Silmaril.Proofs.Wasm.Game.HandleAccept
