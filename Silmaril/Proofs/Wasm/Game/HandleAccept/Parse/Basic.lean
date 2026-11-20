module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Defs
public import Silmaril.Semantics.Accept.Host.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic

/-! # Proofs: one-shot parsing exports -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Accept
  Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Host
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood)
open Silmaril.Wasm.Logic.GameLink (GameSat)

/-! ## Export events -/

variable {E F : Sig.{0}} {Ev : Type}

theorem mem_exportEvents {dec : (f : F.Op) → F.Ar f → Option Ev} {ev : Ev} :
    ∀ {p : List (Move E F)}, ev ∈ exportEvents dec p →
      ∃ f v, (.inr (.ans f v) : Move E F) ∈ p ∧ dec f v = some ev
  | [], h => by simp [exportEvents] at h
  | .inr (.ans f v) :: p, h => by
      simp only [exportEvents, List.mem_append, Option.mem_toList] at h
      rcases h with h | h
      · exact ⟨f, v, List.mem_cons_self, h⟩
      · obtain ⟨f', v', hm, hd⟩ := mem_exportEvents h
        exact ⟨f', v', List.mem_cons_of_mem _ hm, hd⟩
  | .inr (.ask _) :: p, h => by
      obtain ⟨f', v', hm, hd⟩ := mem_exportEvents (p := p) (by simpa [exportEvents] using h)
      exact ⟨f', v', List.mem_cons_of_mem _ hm, hd⟩
  | .inl _ :: p, h => by
      obtain ⟨f', v', hm, hd⟩ := mem_exportEvents (p := p) (by simpa [exportEvents] using h)
      exact ⟨f', v', List.mem_cons_of_mem _ hm, hd⟩

/-! ## The decoder -/

variable {V : Type} {ts : List FnType}

theorem parseDec_oneShot {ix : ParseExports V} (h1 : ix.OneShot) {f : (ifaceSig ts).Op}
    {v : (ifaceSig ts).Ar f} {ev : PEv V (BitVec 32)} (h : parseDec ix f v = some ev) :
    (∃ w h, ev = .parse w h) ∨ ev = .reset := by
  obtain ⟨ha, hd, hf, hfi⟩ := h1
  unfold parseDec at h
  rcases hv : ansVals v with _ | vs <;> simp only [hv, Option.bind_eq_bind, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  simp only [ha, hd, hf, hfi, reduceCtorEq, ite_false] at h
  split_ifs at h
  · rcases hw : ix.val f.2.1 with _ | w <;> rcases hr : i32Res vs with _ | r <;>
      simp [hw, hr] at h
    exact .inl ⟨w, r, h.symm⟩
  · cases h; exact .inr rfl

/-! ## One-shot runs -/

variable {H X : Type} [DecidableEq H]

theorem step_oneShot {pol : PPolicy H} (hb : pol.onBadHandle ≠ .ub) {ρ : Env H X}
    {s s' : PState V} {e : PEv V H} {A : Set (List V × X)} (hs : PStep pol ρ s e s' A)
    (hp : s.phase ≠ .chaos) (he : (∃ w h, e = .parse w h) ∨ e = .reset) :
    s'.phase ≠ .chaos ∧ ∀ q ∈ A, ∃ w h, e = .parse w h ∧ h ≠ pol.sentinel ∧ ρ h = some q.2 ∧
      q.1 = [w] := by
  rcases he with ⟨w, h, rfl⟩ | rfl <;> cases hs
  case inl.ret wl h' hl hR hres =>
    simp only [Returns] at hR
    obtain ⟨rfl, rfl, rfl⟩ := hR
    refine ⟨hp, fun q hq => ?_⟩
    unfold resolve at hres
    split_ifs at hres with hh
    · cases hres; simp at hq
    · rcases hx : ρ h' with _ | x <;> simp [hx] at hres
      subst hres
      simp only [Set.mem_singleton_iff] at hq
      subst hq
      exact ⟨w, h', rfl, hh, hx, rfl⟩
  case inl.retBadSessionTrap => exact ⟨by simp, by simp⟩
  case inr.reset => exact ⟨by simp, by simp⟩
  all_goals first
    | (exfalso; simp_all [Returns]; done)
    | (constructor <;> simp_all [Returns])

theorem run_oneShot {pol : PPolicy H} (hb : pol.onBadHandle ≠ .ub) {ρ : Env H X}
    {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)}
    (hr : (parser pol ρ).Run s t s' A) (hp : s.phase ≠ .chaos)
    (ht : ∀ e ∈ t, (∃ w h, e = .parse w h) ∨ e = .reset) :
    ∀ q ∈ A, ∃ w h, PEv.parse w h ∈ t ∧ h ≠ pol.sentinel ∧ ρ h = some q.2 ∧ q.1 = [w] := by
  induction hr with
  | nil => simp
  | cons hs _ ih =>
      obtain ⟨hp', hA⟩ := step_oneShot hb hs hp (ht _ List.mem_cons_self)
      intro q hq
      rcases hq with hq | hq
      · obtain ⟨w, h, rfl, hh⟩ := hA q hq
        exact ⟨w, h, List.mem_cons_self, hh⟩
      · obtain ⟨w, h, hm, hh⟩ :=
          ih hp' (fun e he => ht e (List.mem_cons_of_mem _ he)) q hq
        exact ⟨w, h, List.mem_cons_of_mem _ hm, hh⟩

/-- **One-shot relations come from `parse` events**: without UB on unresolved handles, every
pair of the relation of `parse`/`reset`-only traces in `ρ` is `([v], x)` for a `parse(v)`
event answered with a non-sentinel handle denoting `x`. -/
theorem parseRel_oneShot {pol : PPolicy H} (hb : pol.onBadHandle ≠ .ub) {ρ : Env H X}
    {T : Set (List (PEv V H))} (hT : ∀ t ∈ T, ∀ e ∈ t, (∃ w h, e = .parse w h) ∨ e = .reset) :
    ∀ q ∈ parseRel pol {ρ} T, ∃ t ∈ T, ∃ w h, PEv.parse w h ∈ t ∧ h ≠ pol.sentinel ∧
      ρ h = some q.2 ∧ q.1 = [w] := by
  intro q hq
  rw [parseRel, langOver, Set.mem_iUnion] at hq
  obtain ⟨⟨ρ', hρ'⟩, hq⟩ := hq
  rw [Set.mem_singleton_iff] at hρ'
  subst hρ'
  obtain ⟨t, ht, s, A, hr, hqA⟩ := mem_lang.1 hq
  exact ⟨t, ht, run_oneShot hb hr (by simp [parser, PState.init]) (hT t ht) q hqA⟩

/-! ## The bridge -/

/-- **Soundness of a one-shot parser module from its Hoare-logic obligation.** -/
theorem moduleParseRel_sound_of_gameSat {X : Type} {P : Numerics.Profile} {m : Module}
    {ix : ParseExports V} {pol : PPolicy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) X} {R : Set (List V × X)} {Inv : Store Nat → Prop}
    (hm : GameSat P (Verify.instOf m) Inv (topISpec _) (parseESpec ix pol.sentinel ρ R))
    (hs : Inv (Verify.instOf m).store) (h1 : ix.OneShot) (hb : pol.onBadHandle ≠ .ub) :
    moduleParseRel P m ix pol {ρ} ⊆ R := by
  intro q hq
  obtain ⟨_, ⟨p, hp, rfl⟩, w, h, hm', hh, hx, hw⟩ := parseRel_oneShot hb (fun t ht e he => by
    obtain ⟨p, -, rfl⟩ := ht
    obtain ⟨f, v, -, hd⟩ := mem_exportEvents he
    exact parseDec_oneShot h1 hd) q hq
  have hAG := (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hp).2
  have hP := Silmaril.Proofs.Wasm.Game.HandleAccept.ag_allP hAG (by
    intro o _ hO
    rcases o with (e | ⟨e, v⟩) | (f | ⟨f, v⟩)
    · simp [Move.IsO] at hO
    · trivial
    · trivial
    · simp [Move.IsO] at hO)
  obtain ⟨f, v, hfm, hd⟩ := mem_exportEvents hm'
  have := hP _ hfm trivial w h hd hh _ hx
  obtain ⟨q1, q2⟩ := q
  simp only at hw
  subst hw
  exact this

/-! ## Environment sets -/

/-- A pair of the relation over `Envs` is a pair of the relation of one of them. -/
theorem mem_parseRel_envs {V H X : Type} [DecidableEq H] {pol : PPolicy H}
    {Envs : Set (Silmaril.Accept.Handle.Env H X)} {T : Set (List (PEv V H))} {q : List V × X}
    (hq : q ∈ parseRel pol Envs T) : ∃ ρ ∈ Envs, q ∈ parseRel pol {ρ} T := by
  rw [parseRel, langOver, Set.mem_iUnion] at hq
  obtain ⟨⟨ρ, hρ⟩, hq⟩ := hq
  refine ⟨ρ, hρ, ?_⟩
  rw [parseRel, langOver, Set.mem_iUnion]
  exact ⟨⟨ρ, rfl⟩, hq⟩

/-- **One-shot parser modules relate only one-value inputs** (every module, profile and
environment set; no obligation). -/
theorem moduleParseRel_input_oneShot {V X : Type} {P : Numerics.Profile} {m : Module}
    {ix : ParseExports V} {pol : PPolicy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)} (h1 : ix.OneShot)
    (hb : pol.onBadHandle ≠ .ub) :
    inputLang (moduleParseRel P m ix pol Envs) ⊆ {w | ∃ v, w = [v]} := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨ρ, -, hq⟩ := mem_parseRel_envs hq
  obtain ⟨_, -, w, -, -, -, -, hw⟩ := parseRel_oneShot hb (fun t ht e he => by
    obtain ⟨p, -, rfl⟩ := ht
    obtain ⟨f, v, -, hd⟩ := mem_exportEvents he
    exact parseDec_oneShot h1 hd) q hq
  exact ⟨w, hw⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing
