module

public import Silmaril.Semantics.Accept.Handle.Defs
public import Silmaril.Semantics.Accept.Host.Thms
import Silmaril.Proofs.Semantics.Accept.Handle.Writer

/-! # Proofs: reader policies, correct reads, certificates, combined sessions, node
environments -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

universe u v w x

section Reader

variable {Q : Type u} {A : Type v} {H : Type w} {X : Type x} {R : Reader Q A H X}

theorem answers_valid {pol : OnBadRead Q A} {ρ : Env H X} {q : Q} (hv : R.valid ρ q) :
    answers R pol ρ q = some {a | R.ok ρ q a} := by
  simp [answers, hv]

theorem answers_invalid {pol : OnBadRead Q A} {ρ : Env H X} {q : Q} (hv : ¬ R.valid ρ q) :
    answers R pol ρ q = badAnswers pol q := by
  simp [answers, hv]

theorem answers_le {pol pol' : OnBadRead Q A} (hle : OnBadRead.Le pol pol') {ρ : Env H X} {q : Q}
    {S : Set A} (hS : answers R pol ρ q = some S) :
    (∃ S', answers R pol' ρ q = some S' ∧ S ⊆ S') ∨ answers R pol' ρ q = none := by
  by_cases hv : R.valid ρ q
  · rw [answers_valid hv] at hS
    cases hS; exact .inl ⟨_, answers_valid hv, le_rfl⟩
  · rw [answers_invalid hv] at hS
    cases hle with
    | refl => exact .inl ⟨S, by rw [answers_invalid hv]; exact hS, le_rfl⟩
    | trap =>
        simp only [badAnswers, Option.some.injEq] at hS; subst hS
        rcases (answers R pol' ρ q) with _ | S'
        · exact .inr rfl
        · exact .inl ⟨S', rfl, Set.empty_subset _⟩
    | dflt d => exact .inl ⟨Set.univ, by rw [answers_invalid hv]; rfl, Set.subset_univ _⟩
    | ub => exact .inr (by rw [answers_invalid hv]; rfl)

theorem answers_none_le {pol pol' : OnBadRead Q A} (hle : OnBadRead.Le pol pol') {ρ : Env H X}
    {q : Q} (hS : answers R pol ρ q = none) : answers R pol' ρ q = none := by
  by_cases hv : R.valid ρ q
  · rw [answers_valid hv] at hS; cases hS
  · rw [answers_invalid hv] at hS ⊢
    cases hle with
    | refl => exact hS
    | trap => cases hS
    | dflt d => cases hS
    | ub => rfl

theorem sim_reader_le {pol pol' : OnBadRead Q A} (hle : OnBadRead.Le pol pol')
    {oa oa' : OnInvalid} (ha : oa.rank ≤ oa'.rank) (ρ : Env H X) :
    Sim (reader R pol oa ρ) (reader R pol' oa' ρ) id
      (fun p₁ p₂ => p₁ = p₂ ∨ p₁ = .dead ∨ p₂ = .chaos ∨ (p₁ = .aborted ∧ p₂ = .live)) := by
  refine ⟨.inl rfl, ?_⟩
  rintro p₁ p₂ e p₁' S hR hs
  rcases hR with rfl | rfl | rfl | ⟨rfl, rfl⟩
  · cases hs with
    | read hS ha' =>
        rcases answers_le hle hS with ⟨S', hS', hsub⟩ | hn
        · exact ⟨_, _, .read hS' (hsub ha'), .inl rfl, le_rfl⟩
        · exact ⟨_, _, .readChaos hn, .inr (.inr (.inl rfl)), Set.empty_subset _⟩
    | readChaos hn => exact ⟨_, _, .readChaos (answers_none_le hle hn), .inl rfl, le_rfl⟩
    | acceptOk h => exact ⟨_, _, .acceptOk h, .inl rfl, le_rfl⟩
    | acceptSessionTrap h hp =>
        rcases hoa : oa' with _ | _ | _ | _
        · exact ⟨_, _, .acceptSessionTrap h rfl, .inl rfl, le_rfl⟩
        · exact ⟨_, _, .acceptCallTrap h rfl, .inr (.inl rfl), le_rfl⟩
        · exact ⟨_, _, .acceptIgnore h rfl, .inr (.inl rfl), le_rfl⟩
        · exact ⟨_, _, .acceptChaos h rfl, .inr (.inr (.inl rfl)), Set.empty_subset _⟩
    | acceptCallTrap h hp =>
        rcases hoa : oa' with _ | _ | _ | _
        · subst hp; simp [OnInvalid.rank, hoa] at ha
        · exact ⟨_, _, .acceptCallTrap h rfl, .inl rfl, le_rfl⟩
        · exact ⟨_, _, .acceptIgnore h rfl, .inr (.inr (.inr ⟨rfl, rfl⟩)), le_rfl⟩
        · exact ⟨_, _, .acceptChaos h rfl, .inr (.inr (.inl rfl)), Set.empty_subset _⟩
    | acceptIgnore h hp =>
        rcases hoa : oa' with _ | _ | _ | _
        · subst hp; simp [OnInvalid.rank, hoa] at ha
        · subst hp; simp [OnInvalid.rank, hoa] at ha
        · exact ⟨_, _, .acceptIgnore h rfl, .inl rfl, le_rfl⟩
        · exact ⟨_, _, .acceptChaos h rfl, .inr (.inr (.inl rfl)), Set.empty_subset _⟩
    | acceptChaos h hp =>
        rcases hoa : oa' with _ | _ | _ | _
        · subst hp; simp [OnInvalid.rank, hoa] at ha
        · subst hp; simp [OnInvalid.rank, hoa] at ha
        · subst hp; simp [OnInvalid.rank, hoa] at ha
        · exact ⟨_, _, .acceptChaos h rfl, .inl rfl, le_rfl⟩
    | enter => exact ⟨_, _, .enter, .inl rfl, le_rfl⟩
    | resume => exact ⟨_, _, .resume, .inl rfl, le_rfl⟩
    | chaos e => exact ⟨_, _, .chaos e, .inl rfl, le_rfl⟩
  · cases hs
  · exact ⟨_, _, .chaos e, .inr (.inr (.inl rfl)), Set.subset_univ _⟩
  · cases hs with
    | resume => exact ⟨_, _, .enter, .inl rfl, le_rfl⟩

theorem readerLang_mono {pol pol' : OnBadRead Q A} (hle : OnBadRead.Le pol pol')
    {oa oa' : OnInvalid} (ha : oa.rank ≤ oa'.rank) {Envs Envs' : Set (Env H X)}
    (hE : Envs ⊆ Envs') (T : Set (List (REv Q A H))) :
    readerLang R pol oa Envs T ⊆ readerLang R pol' oa' Envs' T := by
  intro x hx
  simp only [readerLang, langOver, Set.mem_iUnion] at hx ⊢
  obtain ⟨ρ, hx⟩ := hx
  exact ⟨⟨ρ.1, hE ρ.2⟩, lang_subset_of_sim_id (sim_reader_le hle ha ρ.1) T hx⟩

/-- Under the trapping policies every read of a run is a correct answer and the run never
reaches chaos. -/
theorem trap_facts {oa : OnInvalid} (hoa : oa ≠ .ub) {ρ : Env H X} :
    ∀ {p p' : Phase} {t : List (REv Q A H)} {S : Set X}, (reader R .trap oa ρ).Run p t p' S →
      p ≠ .chaos → p' ≠ .chaos ∧ ∀ qa ∈ REv.reads t, R.valid ρ qa.1 ∧ R.ok ρ qa.1 qa.2 := by
  intro p p' t S hr hp
  induction hr with
  | nil => exact ⟨hp, by simp [REv.reads]⟩
  | cons hs hrest ih =>
      cases hs with
      | @read q a S' hS ha =>
          obtain ⟨h1, h2⟩ := ih (by simp)
          refine ⟨h1, ?_⟩
          by_cases hv : R.valid ρ q
          · rw [answers_valid hv] at hS
            cases hS
            intro qa hqa
            simp only [REv.reads, List.mem_cons] at hqa
            rcases hqa with rfl | hqa
            · exact ⟨hv, ha⟩
            · exact h2 qa hqa
          · rw [answers_invalid hv] at hS; cases hS; simp at ha
      | @readChaos q a hn =>
          by_cases hv : R.valid ρ q
          · rw [answers_valid hv] at hn; cases hn
          · rw [answers_invalid hv] at hn; cases hn
      | acceptOk _ => exact ih (by simp)
      | acceptCallTrap _ _ => exact ih (by simp)
      | acceptSessionTrap _ _ => exact ih (by simp)
      | enter => exact ih (by simp)
      | resume => exact ih (by simp)
      | acceptIgnore _ _ => exact ih (by simp)
      | acceptChaos _ h => exact absurd h hoa
      | chaos _ => exact absurd rfl hp

/-- **Certified acceptance is sound** under the trapping read policy. -/
theorem readerLang_trap_subset {oa : OnInvalid} (hoa : oa ≠ .ub)
    {cert : List (Q × A) → H → Prop} {L : Set X} (hc : CertSound R cert L)
    {T : Set (List (REv Q A H))} (hT : Certified cert T) (Envs : Set (Env H X)) :
    readerLang R .trap oa Envs T ⊆ L := by
  intro x hx
  unfold readerLang langOver at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨⟨ρ, _⟩, hx⟩ := hx
  rw [mem_lang] at hx
  obtain ⟨t, ht, p, S, hr, hxS⟩ := hx
  obtain ⟨u, e, v, p₁, p₂, B, C, rfl, hu, he, hxC⟩ :=
    Host.Run.mem_split (h := reader R .trap oa ρ) hr hxS
  obtain ⟨hp₁, hfacts⟩ := trap_facts hoa hu (by simp [reader])
  cases he with
  | read _ _ => simp at hxC
  | @readChaos q a hn =>
      by_cases hv : R.valid ρ q
      · rw [answers_valid hv] at hn; cases hn
      · rw [answers_invalid hv] at hn; cases hn
  | @acceptOk h t' hρ =>
      simp only [Set.mem_singleton_iff] at hxC; subst hxC
      exact hc ρ _ h hfacts (hT _ ht u v h rfl) _ hρ
  | acceptCallTrap _ _ => simp at hxC
  | acceptSessionTrap _ _ => simp at hxC
  | enter => simp at hxC
  | resume => simp at hxC
  | acceptIgnore _ _ => simp at hxC
  | acceptChaos _ h => exact absurd h hoa
  | chaos _ => exact absurd rfl hp₁

/-- Under a default-answer policy, an answer different from the default is correct; with a
typed error (`ErrorDisjoint`) the default answer is exactly an invalid query. -/
theorem dflt_read {d : Q → A} {ρ : Env H X} {q : Q} {a : A} {S : Set A}
    (hS : answers R (.dflt d) ρ q = some S) (ha : a ∈ S) :
    (R.valid ρ q ∧ R.ok ρ q a) ∨ (¬ R.valid ρ q ∧ a = d q) := by
  by_cases hv : R.valid ρ q
  · rw [answers_valid hv] at hS; cases hS; exact .inl ⟨hv, ha⟩
  · rw [answers_invalid hv] at hS; cases hS; exact .inr ⟨hv, ha⟩

theorem error_iff_invalid {d : Q → A} (hd : ErrorDisjoint R d) {ρ : Env H X} {q : Q} {a : A}
    {S : Set A} (hS : answers R (.dflt d) ρ q = some S) (ha : a ∈ S) :
    a = d q ↔ ¬ R.valid ρ q := by
  rcases dflt_read hS ha with ⟨hv, hok⟩ | ⟨hv, rfl⟩
  · exact ⟨fun e => absurd e (hd ρ q a hok), fun h => absurd hv h⟩
  · exact ⟨fun _ => hv, fun _ => rfl⟩

/-- Away from export calls, a call-local trap step is a session-abort step. -/
theorem rstep_callTrap_sessionTrap {pol : OnBadRead Q A} {ρ : Env H X} {p p' : Phase}
    {e : REv Q A H} {S : Set X} (he : e ≠ .enter) (hs : RStep R pol .callTrap ρ p e p' S) :
    ∃ p'', RStep R pol .sessionTrap ρ p e p'' S ∧ (p'' = p' ∨ (p' = .aborted ∧ p'' = .dead)) := by
  cases hs with
  | read hS ha => exact ⟨_, .read hS ha, .inl rfl⟩
  | readChaos hn => exact ⟨_, .readChaos hn, .inl rfl⟩
  | acceptOk h => exact ⟨_, .acceptOk h, .inl rfl⟩
  | acceptCallTrap h _ => exact ⟨_, .acceptSessionTrap h rfl, .inr ⟨rfl, rfl⟩⟩
  | acceptSessionTrap _ hp => cases hp
  | acceptIgnore _ hp => cases hp
  | acceptChaos _ hp => cases hp
  | enter => exact absurd rfl he
  | resume => exact absurd rfl he
  | chaos e => exact ⟨_, .chaos e, .inl rfl⟩

theorem run_reader_callTrap_sessionTrap {pol : OnBadRead Q A} {ρ : Env H X} :
    ∀ {p p' : Phase} {t : List (REv Q A H)} {S : Set X},
      (reader R pol .callTrap ρ).Run p t p' S → REv.enter ∉ t →
      ∃ p'', (reader R pol .sessionTrap ρ).Run p t p'' S := by
  intro p p' t S hr ht
  induction hr with
  | nil p => exact ⟨p, .nil p⟩
  | @cons p p₁ p₂ e es S B hs hrest ih =>
      have he : e ≠ .enter := fun h => ht (h ▸ List.mem_cons_self)
      have hes : REv.enter ∉ es := fun h => ht (List.mem_cons_of_mem _ h)
      obtain ⟨p'', hs'', rfl | ⟨rfl, rfl⟩⟩ := rstep_callTrap_sessionTrap he hs
      · obtain ⟨p₃, hr₃⟩ := ih hes
        exact ⟨p₃, .cons hs'' hr₃⟩
      · cases hrest with
        | nil => exact ⟨_, .cons hs'' (.nil _)⟩
        | cons hs' _ =>
            cases hs' with
            | resume => exact absurd List.mem_cons_self hes

/-- **Call-local and session abort agree within one export call** (readers). -/
theorem readerLang_callTrap_eq_sessionTrap (pol : OnBadRead Q A) (Envs : Set (Env H X))
    {T : Set (List (REv Q A H))} (hT : ∀ t ∈ T, REv.enter ∉ t.tail) :
    readerLang R pol .callTrap Envs T = readerLang R pol .sessionTrap Envs T := by
  apply Set.Subset.antisymm _
    (readerLang_mono (.refl pol) (by decide) le_rfl T)
  intro x hx
  simp only [readerLang, langOver, Set.mem_iUnion] at hx ⊢
  obtain ⟨ρ, hx⟩ := hx
  refine ⟨ρ, ?_⟩
  obtain ⟨t, ht, p, S, hr, hxS⟩ := mem_lang.1 hx
  refine mem_lang.2 ⟨t, ht, ?_⟩
  have htl := hT t ht
  rcases t with _ | ⟨e, es⟩
  · exact ⟨p, S, by cases hr; exact .nil _, hxS⟩
  · by_cases he : e = .enter
    · subst he
      cases hr with
      | cons hs hrest =>
          obtain ⟨p'', hr''⟩ := run_reader_callTrap_sessionTrap hrest htl
          cases hs with
          | enter => exact ⟨p'', _, .cons .enter hr'', hxS⟩
    · obtain ⟨p'', hr''⟩ := run_reader_callTrap_sessionTrap hr
        (fun h => (List.mem_cons.1 h).elim (fun h' => he h'.symm) htl)
      exact ⟨p'', S, hr'', hxS⟩

end Reader

/-! ## Combined sessions -/

section Combined

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H] {Q : Type u} {A : Type u}
variable {W : Writer Op X} {R : Reader Q A H X} {pol : Policy H} {rpol : OnBadRead Q A}

theorem cstep_extends {s s' : WState H X} {e : CEv Op H Q A} {S : Set X}
    (hs : CStep W R pol rpol s e s' S) : s.store.Extends s'.store := by
  cases hs with
  | w hw => exact wstep_extends hw
  | _ => exact extends_refl _

theorem crun_extends {s s' : WState H X} {t : List (CEv Op H Q A)} {S : Set X}
    (hr : (combined W R pol rpol).Run s t s' S) : s.store.Extends s'.store := by
  induction hr with
  | nil => exact extends_refl _
  | cons hs _ ih => exact extends_trans (cstep_extends hs) ih

theorem crun_cut {s s' : WState H X} {t u : List (CEv Op H Q A)} {S : Set X}
    (hr : (combined W R pol rpol).Run s (t ++ u) s' S) :
    ∃ m B C, (combined W R pol rpol).Run s t m B ∧ (combined W R pol rpol).Run m u s' C ∧
      s.store.Extends m.store ∧ m.store.Extends s'.store := by
  obtain ⟨m, B, C, h1, h2, -⟩ := Run.append_inv hr
  exact ⟨m, B, C, h1, h2, crun_extends h1, crun_extends h2⟩

theorem cstep_write {s s' : WState H X} {op : Op} {args : List H} {r : H} {S : Set X}
    (hs : CStep W R pol rpol s (.w (.write op args r)) s' S) (hr : pol.sentinel ≠ some r)
    (hl : s'.phase = .live) :
    ∃ t, W.built s.store op args = some t ∧ s'.store r = some t := by
  cases hs with
  | w hw =>
      cases hw with
      | writeOk hb _ _ => exact ⟨_, hb, by simp⟩
      | writeFail hsn _ => exact absurd hsn hr
      | writeChaos _ _ _ => simp at hl
      | writeFixed _ _ hfix => cases hfix
      | chaos _ => simp at hl

theorem cstep_read {s s' : WState H X} {q : Q} {a : A} {S : Set X}
    (hs : CStep W R pol rpol s (.r q a) s' S) (hl : s'.phase = .live) :
    ∃ S', answers R rpol s.store q = some S' ∧ a ∈ S' := by
  cases hs with
  | read hS ha => exact ⟨_, hS, ha⟩
  | readChaos _ => simp at hl
  | readInChaos => simp at hl

end Combined

end Silmaril.Proofs.Semantics.Accept.Handle
