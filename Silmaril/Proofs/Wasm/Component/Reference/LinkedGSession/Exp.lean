module

public import Silmaril.Wasm.Component.Reference.LinkedGSession.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.Ref

/-!
# The session triple of an exporter

* `noPlainTrap_sessTripleS`, `storeDet_sessTripleS`: the triple has no plain traps, and is
  store-deterministic for a deterministic exporter (`ExpSpec.Det`);
* `rounds_iff_run`: its completed rounds on typed questions, without import calls, are the
  exporter's sessions;
* `obsEq_of_runEq`, `session_eq_iff`: for deterministic exporters with the same typed questions,
  the session objects are equal iff the typed sessions and the divergences after them agree
  (`StratSession.threadS_eq_iff`; the bisimulation relates the end states of one typed session);
* `mem_inf_session`, `mem_inf_session_iff`: the infinite plays are the coherent infinite
  sequences of rounds, and those of a typed stream are its runs.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Rounds StoreDet InfRounds ObsEq IsBisim RoundEq)
open Silmaril.Games.Abstract.StratSession (NoPlainTrap threadS sroundsPlay sroundsMoves)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {e e' : ExpSpec}

/-! ## The triple -/

theorem sumAns_inj {R R' : Option Payload} (h : ExpSpec.sumAns R = ExpSpec.sumAns R') :
    R = R' := by
  cases R <;> cases R' <;> simp_all [ExpSpec.sumAns]

theorem mem_sessFin {s : e.St} {q : Nat × Payload}
    {x : CallBeh (sigN 0) e.St (Payload ⊕ PUnit.{1})} :
    x ∈ (e.sessTripleS P).1 s q ↔ x.1 = [] ∧ ((¬ e.TypedQ q ∧ x.2 = .ret (.inr PUnit.unit) s) ∨
      (e.TypedQ q ∧ ((∃ (R : Option Payload) (s' : e.St), e.Step P s ⟨q, R⟩ s' ∧
          x.2 = .ret (ExpSpec.sumAns R) s') ∨ (e.DivStep P s q ∧ x.2 = .div)))) :=
  Iff.rfl

theorem ret_mem_typed {s s₁ : e.St} {q : Nat × Payload} {c : List (Call (sigN 0))}
    {b : Payload ⊕ PUnit.{1}} (hq : e.TypedQ q) :
    (c, End.ret b s₁) ∈ (e.sessTripleS P).1 s q ↔
      c = [] ∧ ∃ R, e.Step P s ⟨q, R⟩ s₁ ∧ b = ExpSpec.sumAns R := by
  rw [mem_sessFin]
  constructor
  · rintro ⟨hc, ⟨hn, -⟩ | ⟨-, ⟨R, s', hs, he⟩ | ⟨-, he⟩⟩⟩
    · exact absurd hq hn
    · simp only [End.ret.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hc, R, hs, rfl⟩
    · cases he
  · rintro ⟨rfl, R, hs, rfl⟩
    exact ⟨rfl, .inr ⟨hq, .inl ⟨R, s₁, hs, rfl⟩⟩⟩

theorem ret_mem_untyped {s s₁ : e.St} {q : Nat × Payload} {c : List (Call (sigN 0))}
    {b : Payload ⊕ PUnit.{1}} (hq : ¬ e.TypedQ q) :
    (c, End.ret b s₁) ∈ (e.sessTripleS P).1 s q ↔ c = [] ∧ b = .inr PUnit.unit ∧ s₁ = s := by
  rw [mem_sessFin]
  constructor
  · rintro ⟨hc, ⟨-, he⟩ | ⟨h, -⟩⟩
    · simp only [End.ret.injEq] at he
      exact ⟨hc, he.1, he.2⟩
    · exact absurd h hq
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, .inl ⟨hq, rfl⟩⟩

theorem div_mem {s : e.St} {q : Nat × Payload} {c : List (Call (sigN 0))} :
    (c, End.div) ∈ (e.sessTripleS P).1 s q ↔ c = [] ∧ e.TypedQ q ∧ e.DivStep P s q := by
  rw [mem_sessFin]
  constructor
  · rintro ⟨hc, ⟨-, he⟩ | ⟨h, ⟨_, _, _, he⟩ | ⟨hd, -⟩⟩⟩
    · cases he
    · cases he
    · exact ⟨hc, h, hd⟩
  · rintro ⟨rfl, h, hd⟩
    exact ⟨rfl, .inr ⟨h, .inr ⟨hd, rfl⟩⟩⟩

theorem noPlainTrap_sessTripleS : NoPlainTrap (e.sessTripleS P) := by
  intro s q c h
  obtain ⟨-, ⟨-, he⟩ | ⟨-, ⟨_, _, _, he⟩ | ⟨-, he⟩⟩⟩ := mem_sessFin.mp h <;> cases he

theorem satP_sessTripleS (s : e.St) (q : Nat × Payload) : satP (e.sessTripleS P) s q = ∅ := by
  ext x
  exact x.2.1.elim0

/-- **Store determinism** of the triple of a deterministic exporter. -/
theorem storeDet_sessTripleS (hd : e.Det P) : StoreDet (e.sessTripleS P) := by
  intro s q c b s₁ s₂ h₁ h₂
  by_cases hq : e.TypedQ q
  · obtain ⟨-, R₁, hs₁, -⟩ := (ret_mem_typed hq).mp h₁
    obtain ⟨-, R₂, hs₂, -⟩ := (ret_mem_typed hq).mp h₂
    exact (hd hs₁ hs₂).2
  · rw [((ret_mem_untyped hq).mp h₁).2.2, ((ret_mem_untyped hq).mp h₂).2.2]

/-! ## Rounds and sessions -/

/-- A typed round as a completed session round without import calls. -/
abbrev toSR (r : URound) : (Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit.{1}) :=
  (r.1, [], ExpSpec.sumAns r.2)

/-- **Completed rounds of typed questions are sessions.** -/
theorem rounds_iff_run : ∀ {s s' : e.St} {L : List URound}, (∀ r ∈ L, e.Typed r) →
    (Rounds (e.sessTripleS P) s (L.map toSR) s' ↔ e.Run P s L s')
  | s, s', [], _ => ⟨fun h => by cases h; exact .nil _, fun h => by cases h; exact .nil _⟩
  | s, s', r :: L, ht => by
    have hL : ∀ x ∈ L, e.Typed x := fun x hx => ht x (List.mem_cons_of_mem _ hx)
    have hr : e.TypedQ r.1 := ht r List.mem_cons_self
    rw [List.map_cons]
    constructor
    · intro h
      cases h with
      | cons hm hrs =>
        obtain ⟨-, R, hs, he⟩ := (ret_mem_typed hr).mp hm
        obtain rfl := sumAns_inj he
        exact .cons hs ((rounds_iff_run hL).mp hrs)
    · intro h
      cases h with
      | cons hs hrs =>
        exact .cons ((ret_mem_typed hr).mpr ⟨rfl, _, hs, rfl⟩) ((rounds_iff_run hL).mpr hrs)

/-! ## Equal sessions -/

section Bisim

/-- Returns matched along a relation carry typed sessions. -/
theorem run_of_ret {B : e.St → e'.St → Prop} (hq : ∀ q, e.TypedQ q → e'.TypedQ q)
    (hret : ∀ s s', B s s' → ∀ a c b s₁, (c, End.ret b s₁) ∈ (e.sessTripleS P).1 s a →
      ∃ s₁', (c, End.ret b s₁') ∈ (e'.sessTripleS P).1 s' a ∧ B s₁ s₁') :
    ∀ ⦃s s₁ : e.St⦄ ⦃L : List URound⦄, e.Run P s L s₁ → ∀ ⦃s' : e'.St⦄,
      (∀ r ∈ L, e.Typed r) → B s s' → ∃ s₁', e'.Run P s' L s₁' ∧ B s₁ s₁' := by
  intro s s₁ L h
  induction h with
  | nil => exact fun s' _ hB => ⟨s', .nil _, hB⟩
  | @cons s s₂ _ r L hs _ ih =>
    intro s' ht hB
    have hr : e.TypedQ r.1 := ht r List.mem_cons_self
    obtain ⟨s₂', hm', hB₂⟩ := hret s s' hB r.1 [] _ s₂ ((ret_mem_typed hr).mpr ⟨rfl, r.2, hs, rfl⟩)
    obtain ⟨-, R, hs', he⟩ := (ret_mem_typed (hq _ hr)).mp hm'
    obtain rfl := sumAns_inj he
    obtain ⟨s₁', h', hB₁⟩ := ih (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hB₂
    exact ⟨s₁', .cons hs' h', hB₁⟩

/-- A typed return matched by an exporter with the same typed sessions. -/
theorem ret_match (hd' : e'.Det P) (hq : ∀ q, e.TypedQ q → e'.TypedQ q)
    (hnq : ∀ q, e'.TypedQ q → e.TypedQ q)
    (hR : ∀ L : List URound, (∀ r ∈ L, e.Typed r) → (∃ s, e.Run P e.init L s) →
      ∃ s', e'.Run P e'.init L s')
    {L : List URound} (ht : ∀ r ∈ L, e.Typed r) {s : e.St} {s' : e'.St}
    (h : e.Run P e.init L s) (h' : e'.Run P e'.init L s') {a : Nat × Payload}
    {c : List (Call (sigN 0))} {b : Payload ⊕ PUnit.{1}} {s₁ : e.St}
    (hm : (c, End.ret b s₁) ∈ (e.sessTripleS P).1 s a) :
    ∃ s₁', (c, End.ret b s₁') ∈ (e'.sessTripleS P).1 s' a ∧
      ∃ L₁ : List URound, (∀ r ∈ L₁, e.Typed r) ∧ e.Run P e.init L₁ s₁ ∧
        e'.Run P e'.init L₁ s₁' := by
  by_cases ha : e.TypedQ a
  · obtain ⟨rfl, R, hs, rfl⟩ := (ret_mem_typed ha).mp hm
    have ht₁ : ∀ r ∈ L ++ [⟨a, R⟩], e.Typed r := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact ht r hr
      · rw [List.mem_singleton.mp hr]
        exact ha
    have h₁ : e.Run P e.init (L ++ [⟨a, R⟩]) s₁ := LinkedG.run_append h (.cons hs (.nil _))
    obtain ⟨t₁, h₁'⟩ := hR _ ht₁ ⟨s₁, h₁⟩
    obtain ⟨m, hm', hl⟩ := LinkedG.run_split L [_] h₁'
    obtain rfl := LinkedGChatter.run_functional hd' h' hm'
    exact ⟨t₁, (ret_mem_typed (hq a ha)).mpr ⟨rfl, R, LinkedGInf.run_one hl, rfl⟩, _, ht₁, h₁,
      h₁'⟩
  · obtain ⟨rfl, rfl, rfl⟩ := (ret_mem_untyped ha).mp hm
    exact ⟨s', (ret_mem_untyped fun h => ha (hnq a h)).mpr ⟨rfl, rfl, rfl⟩, L, ht, h, h'⟩

/-- A divergence matched by an exporter with the same divergences. -/
theorem div_match (hd' : e'.Det P) (hq : ∀ q, e.TypedQ q → e'.TypedQ q)
    (hD : ∀ (L : List URound) (q : Nat × Payload), (∀ r ∈ L, e.Typed r) → e.TypedQ q →
      (∃ s, e.Run P e.init L s ∧ e.DivStep P s q) → ∃ s', e'.Run P e'.init L s' ∧ e'.DivStep P s' q)
    {L : List URound} (ht : ∀ r ∈ L, e.Typed r) {s : e.St} {s' : e'.St}
    (h : e.Run P e.init L s) (h' : e'.Run P e'.init L s') {a : Nat × Payload}
    {c : List (Call (sigN 0))} (hm : (c, End.div) ∈ (e.sessTripleS P).1 s a) :
    (c, End.div) ∈ (e'.sessTripleS P).1 s' a := by
  obtain ⟨rfl, ha, hds⟩ := div_mem.mp hm
  obtain ⟨s₁, h₁, hds₁⟩ := hD L a ht ha ⟨s, h, hds⟩
  obtain rfl := LinkedGChatter.run_functional hd' h' h₁
  exact div_mem.mpr ⟨rfl, hq a ha, hds₁⟩

end Bisim

theorem typed_of_sameQ (hq : e.SameQ e') {L : List URound} (ht : ∀ r ∈ L, e.Typed r) :
    ∀ r ∈ L, e'.Typed r :=
  fun r hr => (hq r.1).mp (ht r hr)

theorem typed_of_sameQ' (hq : e.SameQ e') {L : List URound} (ht : ∀ r ∈ L, e'.Typed r) :
    ∀ r ∈ L, e.Typed r :=
  fun r hr => (hq r.1).mpr (ht r hr)

/-- **The bisimulation of equal typed sessions and divergences**: the end states of one typed
session from the initial states. -/
theorem obsEq_of_runEq (hd : e.Det P) (hd' : e'.Det P) (hq : e.SameQ e') (hR : e.RunEq P e')
    (hD : e.DivEq P e') : ObsEq (e.sessTripleS P) (e'.sessTripleS P) e.init e'.init := by
  refine ⟨fun s s' => ∃ L, (∀ r ∈ L, e.Typed r) ∧ e.Run P e.init L s ∧ e'.Run P e'.init L s',
    ?_, ?_⟩
  swap
  · exact ⟨[], (fun _ h => nomatch h), .nil _, .nil _⟩
  rintro s s' ⟨L, ht, h, h'⟩
  refine ⟨fun a c => iff_of_false (noPlainTrap_sessTripleS _ _ _) (noPlainTrap_sessTripleS _ _ _),
    fun a c => ⟨fun hm => ?_, fun hm => ?_⟩, ?_, rfl, fun a c b s₁ hm => ?_,
    fun a c b s₁' hm => ?_⟩
  · exact div_match hd' (fun q => (hq q).mp) (fun L q ht hq₁ hx => (hD L q ht hq₁).mp hx) ht h h'
      hm
  · exact div_match hd (fun q => (hq q).mpr)
      (fun L q ht' hq₁ hx => (hD L q (typed_of_sameQ' hq ht') ((hq q).mpr hq₁)).mpr hx)
      (typed_of_sameQ hq ht) h' h hm
  · funext a
    rw [satP_sessTripleS, satP_sessTripleS]
  · obtain ⟨s₁', hm', L₁, ht₁, h₁, h₁'⟩ := ret_match hd' (fun q => (hq q).mp) (fun q => (hq q).mpr)
      (fun L ht hx => (hR L ht).mp hx) ht h h' hm
    exact ⟨s₁', hm', L₁, ht₁, h₁, h₁'⟩
  · obtain ⟨s₁, hm', L₁, ht₁, h₁', h₁⟩ := ret_match hd (fun q => (hq q).mpr) (fun q => (hq q).mp)
      (fun L ht' hx => (hR L (typed_of_sameQ' hq ht')).mpr hx) (typed_of_sameQ hq ht) h' h hm
    exact ⟨s₁, hm', L₁, typed_of_sameQ' hq ht₁, h₁, h₁'⟩

/-- **Equal session objects of deterministic exporters with the same typed questions** are equal
typed sessions and divergences from the initial states. -/
theorem session_eq_iff (hd : e.Det P) (hd' : e'.Det P) (hq : e.SameQ e') :
    e.session P = e'.session P ↔ e.RunEq P e' ∧ e.DivEq P e' := by
  unfold ExpSpec.session
  rw [StratSession.threadS_eq_iff (storeDet_sessTripleS hd) (storeDet_sessTripleS hd')
    noPlainTrap_sessTripleS noPlainTrap_sessTripleS]
  constructor
  · rintro ⟨B, hB, h0⟩
    have fwd := run_of_ret (B := B) (fun q => (hq q).mp) fun s s' hs => (hB s s' hs).ret
    have bwd := run_of_ret (B := fun s' s => B s s') (fun q => (hq q).mpr)
      fun s' s hs => (hB s s' hs).ret'
    refine ⟨fun L ht => ⟨fun ⟨s, h⟩ => ?_, fun ⟨s', h'⟩ => ?_⟩,
      fun L q ht hq₁ => ⟨fun ⟨s, h, hds⟩ => ?_, fun ⟨s', h', hds'⟩ => ?_⟩⟩
    · obtain ⟨s', h', -⟩ := fwd h ht h0
      exact ⟨s', h'⟩
    · obtain ⟨s, h, -⟩ := bwd h' (typed_of_sameQ hq ht) h0
      exact ⟨s, h⟩
    · obtain ⟨s', h', hB'⟩ := fwd h ht h0
      exact ⟨s', h', (div_mem.mp (((hB s s' hB').div q []).mp
        (div_mem.mpr ⟨rfl, hq₁, hds⟩))).2.2⟩
    · obtain ⟨s, h, hB'⟩ := bwd h' (typed_of_sameQ hq ht) h0
      exact ⟨s, h, (div_mem.mp (((hB s s' hB').div q []).mpr
        (div_mem.mpr ⟨rfl, (hq q).mp hq₁, hds'⟩))).2.2⟩
  · rintro ⟨hR, hD⟩
    exact obsEq_of_runEq hd hd' hq hR hD

/-! ## Infinite plays -/

/-- **The infinite plays of the session of a deterministic exporter**: the plays of coherent
infinite sequences of rounds (no productive streams). -/
theorem mem_inf_session (hd : e.Det P) {J : Set (List (Move (sigN 0) sessSig))} :
    J ∈ (e.session P).inf ↔
      ∃ a r s, InfRounds (e.sessTripleS P) e.init a r s ∧ J = sroundsPlay a r := by
  unfold ExpSpec.session
  rw [StratSession.mem_inf_iff_of_storeDet (storeDet_sessTripleS hd)]
  refine or_iff_right ?_
  rintro ⟨_, _, _, _, _, hω, _⟩
  exact hω

theorem streamTake_map_toSR (r : ℕ → URound) (n : ℕ) :
    streamTake (fun i => ((r i).1, (([] : List (Call (sigN 0))), ExpSpec.sumAns (r i).2))) n =
      (streamTake r n).map toSR := by
  simp only [streamTake, List.map_ofFn]
  rfl

theorem typed_streamTake {r : ℕ → URound} (ht : ∀ k, e.Typed (r k)) (n : ℕ) :
    ∀ x ∈ streamTake r n, e.Typed x := by
  intro x hx
  simp only [streamTake, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ht i

/-- **The infinite play of a typed stream of rounds is one of the session object iff the stream
is a run** of the exporter from its initial state (deterministic exporter). -/
theorem mem_inf_session_iff (hd : e.Det P) (r : ℕ → URound) (ht : ∀ k, e.Typed (r k)) :
    sroundsPlay (fun k => (r k).1) (fun k => (([] : List (Call (sigN 0))), ExpSpec.sumAns (r k).2))
        ∈ (e.session P).inf ↔
      ∃ S : ℕ → e.St, S 0 = e.init ∧ ∀ k, e.Step P (S k) (r k) (S (k + 1)) := by
  constructor
  · intro hJ
    refine LinkedGInf.stream_run_of_det hd r e.init fun n => ?_
    have hm := (e.session P).inf_sub hJ ⟨n, List.prefix_refl _⟩
    obtain ⟨s, hs⟩ := (StratSession.mem_srounds_of_noPlainTrap noPlainTrap_sessTripleS).mp hm
    rw [streamTake_map_toSR] at hs
    exact ⟨s, (rounds_iff_run (typed_streamTake ht n)).mp hs⟩
  · rintro ⟨S, h0, hS⟩
    exact StratSession.InfRounds.mem_sinf
      ⟨h0, fun k => (ret_mem_typed (ht k)).mpr ⟨rfl, (r k).2, hS k, rfl⟩⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession
