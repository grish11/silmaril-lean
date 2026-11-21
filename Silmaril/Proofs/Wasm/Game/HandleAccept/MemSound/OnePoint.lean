module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost

/-!
# Proofs: `MemSat` is the one-point case of `GMemSat`

For the one-point ghost `Unit` the relabelling `gConfig ()` is a bijection between real and
specification configurations, with inverse `Config.mapH Prod.fst` (`gConfig_erase`,
`gConfig_unerase`). Steps under related host relations commute with renaming host code
(`step_mapH_host`: host-free steps by `Step.mapH`, a host-call redex by `decompose_mapH` and the
host's own answer), so step-indexed safety transfers in both directions (`safe_unit`,
`safe_erase`) when each host answer of one side is an answer of the other. `memHost` and the
`gHost` of `MemContract.toG` are so related (`memHost_toG`, `gHost_toG`), hence
`memSat_iff_gMemSat`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Strategy (resultOutcome)
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH Config.mapH FuncInst.mapH FuncCode.mapH
  Step.mapH)

variable {X I O C : Type}

/-! ## Renaming host code along steps -/

/-- A redex of `s` is a redex of the renamed store, with renamed host code. -/
theorem decompose_mapH {H H' : Type} (g : H → H') {s : Store H} {code : List Admin}
    {E : SingleThreaded.Ctx} {fa : Nat} {h : H} {args : List Val}
    (hd : decompose? s code = some (E, fa, h, args)) :
    decompose? (Store.mapH g s) code = some (E, fa, g h, args) := by
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ :=
    Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hcode]
  exact decompose_fill' E hyy (fi := FuncInst.mapH g fi)
    (by rw [Silmaril.Proofs.Wasm.Component.Reference.Store.mapH_funcs_getElem?, hf]; rfl)
    he hn (by simp [FuncInst.mapH, hc, FuncCode.mapH])

/-- **Steps commute with renaming host code**, for host relations whose answers are carried
along the renaming. -/
theorem step_mapH_host {P : Numerics.Profile} {H H' : Type} (g : H → H')
    {host : HostSemantics H} {host' : HostSemantics H'}
    (hr : ∀ h s args s' r, host h s args (.returned s' r) →
      host' (g h) (Store.mapH g s) args (.returned (Store.mapH g s') r))
    (hv : ∀ h s args, host h s args .diverged → host' (g h) (Store.mapH g s) args .diverged)
    {c c' : Config H} (hst : Step P host c c') :
    Step P host' (Config.mapH g c) (Config.mapH g c') := by
  rcases Silmaril.Wasm.SingleThreaded.Step.split_host hst with
    h0 | ⟨E, a, h, args, hd, ⟨s', r, hh, rfl⟩ | ⟨hh, he⟩⟩
  · exact Step.of_noHost host' (Step.mapH g h0)
  · exact Silmaril.Wasm.Logic.Open.redex_step_ret
      (show decompose? (Config.mapH g c).store (Config.mapH g c).code = _ from
        decompose_mapH g hd) (hr _ _ _ _ _ hh)
  · rw [he]
    exact Silmaril.Wasm.Logic.Open.redex_step_div
      (show decompose? (Config.mapH g c).store (Config.mapH g c).code = _ from
        decompose_mapH g hd) (hv _ _ _ hh)

/-! ## The one-point ghost -/

theorem gStore_unerase (s : Store (Nat × Unit)) : gStore () (Store.mapH Prod.fst s) = s := by
  rcases s with ⟨t1, g1, m1, tb1, f1, d1, e1, st1, a1, x1⟩
  simp only [gStore, Store.mapH, List.map_map, Store.mk.injEq, true_and, and_true]
  conv_rhs => rw [← List.map_id f1]
  refine List.map_congr_left fun ⟨t, m, c⟩ _ => ?_
  cases c <;> rfl

theorem gConfig_unerase (c : Config (Nat × Unit)) : gConfig () (Config.mapH Prod.fst c) = c := by
  rcases c with ⟨s, f, code⟩
  show (⟨gStore () (Store.mapH Prod.fst s), f, code⟩ : Config (Nat × Unit)) = ⟨s, f, code⟩
  rw [gStore_unerase]

theorem gStore_unit_inj {s s' : Store Nat} {g : Unit} (h : gStore () s = gStore g s') : s = s' := by
  have := congrArg (Store.mapH Prod.fst) h
  rwa [gStore_erase, gStore_erase] at this

/-- **Safety moves to the one-point specification world.** -/
theorem safe_unit {P : Numerics.Profile} {host : HostSemantics Nat}
    {host' : HostSemantics (Nat × Unit)} {Q : Post Nat} {Q' : Post (Nat × Unit)}
    (hr : ∀ h s args s' r, host h s args (.returned s' r) →
      host' (ghostH () h) (gStore () s) args (.returned (gStore () s') r))
    (hv : ∀ h s args, host h s args .diverged → host' (ghostH () h) (gStore () s) args .diverged)
    (hr' : ∀ h s args s' r, host' h s args (.returned s' r) →
      host h.1 (Store.mapH Prod.fst s) args (.returned (Store.mapH Prod.fst s') r))
    (hv' : ∀ h s args, host' h s args .diverged → host h.1 (Store.mapH Prod.fst s) args .diverged)
    (hQ : ∀ s f o, Q s f o → Q' (gStore () s) f o) :
    ∀ {n : Nat} {c : Config Nat}, Safe P host Q n c → Safe P host' Q' n (gConfig () c)
  | 0, _, _ => trivial
  | _ + 1, _, .inl ⟨o, hx, hq⟩ => .inl ⟨o, hx, hQ _ _ _ hq⟩
  | _ + 1, c, .inr ⟨⟨_, hc'⟩, hall⟩ =>
      .inr ⟨⟨_, step_mapH_host (ghostH ()) hr hv hc'⟩, fun c'' h => by
        have h' := step_mapH_host Prod.fst hr' hv' h
        rw [gConfig_erase] at h'
        rw [← gConfig_unerase c'']
        exact safe_unit hr hv hr' hv' hQ (hall _ h')⟩

/-- **Safety moves back to the real world.** -/
theorem safe_erase {P : Numerics.Profile} {host : HostSemantics Nat}
    {host' : HostSemantics (Nat × Unit)} {Q : Post Nat} {Q' : Post (Nat × Unit)}
    (hr : ∀ h s args s' r, host h s args (.returned s' r) →
      host' (ghostH () h) (gStore () s) args (.returned (gStore () s') r))
    (hv : ∀ h s args, host h s args .diverged → host' (ghostH () h) (gStore () s) args .diverged)
    (hr' : ∀ h s args s' r, host' h s args (.returned s' r) →
      host h.1 (Store.mapH Prod.fst s) args (.returned (Store.mapH Prod.fst s') r))
    (hv' : ∀ h s args, host' h s args .diverged → host h.1 (Store.mapH Prod.fst s) args .diverged)
    (hQ : ∀ s f o, Q' (gStore () s) f o → Q s f o) :
    ∀ {n : Nat} {c : Config Nat}, Safe P host' Q' n (gConfig () c) → Safe P host Q n c
  | 0, _, _ => trivial
  | _ + 1, _, .inl ⟨o, hx, hq⟩ => .inl ⟨o, hx, hQ _ _ _ hq⟩
  | _ + 1, c, .inr ⟨⟨_, hc'⟩, hall⟩ =>
      .inr ⟨⟨_, by
          have h' := step_mapH_host Prod.fst hr' hv' hc'
          rw [gConfig_erase] at h'
          exact h'⟩, fun c'' h =>
        safe_erase hr hv hr' hv' hQ (hall _ (step_mapH_host (ghostH ()) hr hv h))⟩

/-! ## `memHost` and the one-point `gHost` -/

variable {m : Module} {memAddr : Option Nat} {R : Roles X I O C} {K : MemContract I}

theorem memHost_toG {h : Nat} {s : Store Nat} {args : List Val}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Store Nat) Result}
    {o' : Silmaril.Wasm.Execution.Host.Outcome (Store (Nat × Unit)) Result}
    (ho : ∀ s' r, o = .returned s' r → o' = .returned (gStore () s') r)
    (hd : o = .diverged → o' = .diverged)
    (hh : memHost m memAddr R K h s args o) :
    gHost m memAddr R K.toG (ghostH () h) (gStore () s) args o' := by
  obtain ⟨S, hS, hpre, hpost⟩ := hh
  simp only [memCtx, id, Option.map_eq_some_iff] at hS
  obtain ⟨i, hi, rfl⟩ := hS
  refine ⟨gImportSpec h i memAddr R K.toG, by simp [gCtx, ghostH, hi], ⟨(), s, rfl, hpre⟩, ?_⟩
  cases o with
  | returned s' r =>
      rw [ho s' r rfl]
      obtain ⟨r', hr', hrep, hans⟩ := hpost
      exact ⟨(), s, rfl, r', s', hr', rfl, hrep, hans⟩
  | diverged => rw [hd rfl]; trivial

theorem gHost_toG {h : Nat × Unit} {s : Store (Nat × Unit)} {args : List Val}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Store (Nat × Unit)) Result}
    {o' : Silmaril.Wasm.Execution.Host.Outcome (Store Nat) Result}
    (ho : ∀ s' r, o = .returned s' r → o' = .returned (Store.mapH Prod.fst s') r)
    (hd : o = .diverged → o' = .diverged)
    (hh : gHost m memAddr R K.toG h s args o) :
    memHost m memAddr R K h.1 (Store.mapH Prod.fst s) args o' := by
  obtain ⟨S, hS, hpre, hpost⟩ := hh
  simp only [gCtx, Option.map_eq_some_iff] at hS
  obtain ⟨i, hi, rfl⟩ := hS
  obtain ⟨g, sR, rfl, hpre⟩ := hpre
  refine ⟨importSpec h.1 i memAddr R K, by simp [memCtx, hi], by rwa [gStore_erase], ?_⟩
  cases o with
  | returned s' r =>
      rw [ho s' r rfl]
      obtain ⟨g', sR₂, hs, r', sR', hr', rfl, hrep, hans⟩ := hpost
      obtain rfl := gStore_unit_inj (g := g') (by cases g; exact hs)
      rw [gStore_erase, gStore_erase]
      exact ⟨r', hr', hrep, hans⟩
  | diverged => rw [hd rfl]; trivial

/-! ## The equivalence -/

variable {P : Numerics.Profile} {memIdx : Nat} {Inv : Store Nat → Prop}

theorem post_toG {Inv : Store Nat → Prop} {s : Store Nat} (h : Inv s) :
    ∀ g sR, gStore () s = gStore g sR → Inv sR := fun _ _ he => gStore_unit_inj he ▸ h

theorem memSat_iff_gMemSat :
    MemSat P m memIdx R K Inv ↔ GMemSat P m memIdx R K.toG (fun _ => Inv) () := by
  have hr : ∀ {ma : Option Nat} h s args s' r, memHost m ma R K h s args (.returned s' r) →
      gHost m ma R K.toG (ghostH () h) (gStore () s) args (.returned (gStore () s') r) :=
    fun _ _ _ _ _ hh => memHost_toG (by intro _ _ h; cases h; rfl) (by intro h; cases h) hh
  have hv : ∀ {ma : Option Nat} h s args, memHost m ma R K h s args .diverged →
      gHost m ma R K.toG (ghostH () h) (gStore () s) args .diverged :=
    fun _ _ _ hh => memHost_toG (by intro _ _ h; cases h) (fun _ => rfl) hh
  have hr' : ∀ {ma : Option Nat} (h : Nat × Unit) s args s' r,
      gHost m ma R K.toG h s args (.returned s' r) →
      memHost m ma R K h.1 (Store.mapH Prod.fst s) args (.returned (Store.mapH Prod.fst s') r) :=
    fun _ _ _ _ _ hh => gHost_toG (by intro _ _ h; cases h; rfl) (by intro h; cases h) hh
  have hv' : ∀ {ma : Option Nat} (h : Nat × Unit) s args, gHost m ma R K.toG h s args .diverged →
      memHost m ma R K h.1 (Store.mapH Prod.fst s) args .diverged :=
    fun _ _ _ hh => gHost_toG (by intro _ _ h; cases h) (fun _ => rfl) hh
  constructor
  · intro hsat mt Is c₀ hc₀
    obtain ⟨hi, he⟩ := hsat mt Is c₀ hc₀
    refine ⟨fun n => safe_unit hr hv hr' hv' ?_ (hi n), fun a ha n s args hpre f vs₀ c hc => ?_⟩
    · intro s f o hq vs ho
      exact post_toG (hq vs ho)
    · obtain ⟨g, sR, rfl, hI, hok⟩ := hpre
      cases g
      refine safe_unit (c := ⟨sR, f, _⟩) hr hv hr' hv' ?_ (he a ha n sR args ⟨hI, hok⟩ f vs₀ c hc)
      rintro s' f' o ⟨rfl, h | h | h⟩
      · obtain ⟨res, rfl, hq⟩ := h; exact ⟨rfl, .inl ⟨res, rfl, post_toG hq⟩⟩
      · obtain ⟨rfl, hq⟩ := h; exact ⟨rfl, .inr (.inl ⟨rfl, post_toG hq⟩)⟩
      · obtain ⟨a, rfl, hq⟩ := h; exact ⟨rfl, .inr (.inr ⟨a, rfl, post_toG hq⟩)⟩
  · intro hsat mt Is c₀ hc₀
    obtain ⟨hi, he⟩ := hsat mt Is c₀ hc₀
    refine ⟨fun n => safe_erase hr hv hr' hv' ?_ (hi n), fun a ha n s args hpre f vs₀ c hc => ?_⟩
    · intro s f o hq vs ho
      exact hq vs ho () s rfl
    · obtain ⟨hI, hok⟩ := hpre
      refine safe_erase (c := ⟨s, f, _⟩) hr hv hr' hv' ?_
        (he a ha n (gStore () s) args ⟨(), s, rfl, hI, hok⟩ f vs₀ c hc)
      rintro s' f' o ⟨rfl, h | h | h⟩
      · obtain ⟨res, rfl, hq⟩ := h; exact ⟨rfl, .inl ⟨res, rfl, hq () s' rfl⟩⟩
      · obtain ⟨rfl, hq⟩ := h; exact ⟨rfl, .inr (.inl ⟨rfl, hq () s' rfl⟩)⟩
      · obtain ⟨a, rfl, hq⟩ := h; exact ⟨rfl, .inr (.inr ⟨a, rfl, hq () s' rfl⟩)⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost
