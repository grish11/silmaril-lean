module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Defs
public import Silmaril.Semantics.Accept.Mixed.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.Parse.Basic

/-! # Proofs: mixed plays and the assume/guarantee bridge -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Mixed
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood)
open Silmaril.Wasm.Logic.GameLink (GameSat)

/-! ## Decoded events -/

section Events

variable {E F : Sig.{0}} {Op V H : Type} {dAsk : E.Op → Option (WEv Op H)}
  {dAns : (e : E.Op) → E.Ar e → Option (WEv Op H)}
  {pdec : (f : F.Op) → F.Ar f → Option (PEv V H)}

/-- A parsing event of a play is the decoding of one of its export answers. -/
theorem p_mem_mixedEvents {pe : PEv V H} :
    ∀ {p : List (Move E F)}, MEv.p pe ∈ mixedEvents dAsk dAns pdec p →
      ∃ f v, (.inr (.ans f v) : Move E F) ∈ p ∧ pdec f v = some pe
  | [], h => by simp [mixedEvents] at h
  | .inl (.ask e) :: p, h => by
      simp only [mixedEvents, List.mem_append] at h
      rcases h with h | h
      · cases hd : dAsk e <;> simp [hd] at h
      · obtain ⟨f, v, hm, hd⟩ := p_mem_mixedEvents h
        exact ⟨f, v, List.mem_cons_of_mem _ hm, hd⟩
  | .inl (.ans e v') :: p, h => by
      simp only [mixedEvents, List.mem_append] at h
      rcases h with h | h
      · cases hd : dAns e v' <;> simp [hd] at h
      · obtain ⟨f, v, hm, hd⟩ := p_mem_mixedEvents h
        exact ⟨f, v, List.mem_cons_of_mem _ hm, hd⟩
  | .inr (.ask _) :: p, h => by
      simp only [mixedEvents, List.mem_cons, reduceCtorEq, false_or] at h
      obtain ⟨f, v, hm, hd⟩ := p_mem_mixedEvents h
      exact ⟨f, v, List.mem_cons_of_mem _ hm, hd⟩
  | .inr (.ans f' v') :: p, h => by
      simp only [mixedEvents, List.mem_append] at h
      rcases h with h | h
      · cases hd : pdec f' v' <;> simp [hd] at h
        subst h
        exact ⟨f', v', List.mem_cons_self, hd⟩
      · obtain ⟨f, v, hm, hd⟩ := p_mem_mixedEvents h
        exact ⟨f, v, List.mem_cons_of_mem _ hm, hd⟩

/-- A decoded import answer is a writer event of the play. -/
theorem ans_mem_mixedEvents {e : E.Op} {v : E.Ar e} {ev : WEv Op H} (hd : dAns e v = some ev) :
    ∀ {p : List (Move E F)}, (.inl (.ans e v) : Move E F) ∈ p →
      MEv.w ev ∈ mixedEvents dAsk dAns pdec p
  | [], h => by simp at h
  | m :: p, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp [mixedEvents, hd]
      · have := ans_mem_mixedEvents hd h
        rcases m with (e' | ⟨e', v'⟩) | (f' | ⟨f', v'⟩) <;>
          simp [mixedEvents, this]

end Events

/-! ## The bridge -/

variable {V : Type} {P : Numerics.Profile} {m : Module} {wix : ConsWImports}
  {pix : ParseExports V} {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)}
  {R : Set (List V × SExp2 (BitVec 64))} {Inv : Store Nat → Prop}

/-- **Per environment**: from the Hoare-logic obligation in `σ`, every decoded trace whose writes
agree with `σ` has its returns related in `σ` (one-shot exports). -/
theorem traces_AG {σ : Env (BitVec 32) (SExp2 (BitVec 64))}
    (hm : GameSat P (Verify.instOf m) Inv (mixedISpec wix pol.sentinel σ)
      (parseESpec pix ppol.sentinel σ R))
    (hs : Inv (Verify.instOf m).store) (h1 : pix.OneShot) :
    ∀ t ∈ moduleMixedTraces P m wix pix,
      WritesAgree (consW (BitVec 64)) pol.sentinel σ t → ReturnsIn ppol σ R t := by
  rintro _ ⟨p, hp, rfl⟩ hW e he ps w h ps' hR hh x hx
  have hAG := (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hp).2
  have hP := Silmaril.Proofs.Wasm.Game.HandleAccept.ag_allP hAG (by
    intro o ho hO
    rcases o with (e' | ⟨e', v⟩) | (f | ⟨f, v⟩)
    · simp [Move.IsO] at hO
    · intro op args r hd
      exact hW op args r (ans_mem_mixedEvents hd ho)
    · trivial
    · simp [Move.IsO] at hO)
  obtain ⟨f, v, hfm, hd⟩ := p_mem_mixedEvents he
  rcases Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.parseDec_oneShot h1 hd with
    ⟨w', h', rfl⟩ | rfl
  · obtain ⟨rfl, rfl, -⟩ := hR
    exact hP _ hfm trivial w' h hd hh x hx
  · exact hR.elim

/-- **Soundness of a parser module building its trees** (store semantics). -/
theorem moduleMixedRel_sound_of_gameSat
    (hm : ∀ σ, GameSat P (Verify.instOf m) Inv (mixedISpec wix pol.sentinel σ)
      (parseESpec pix ppol.sentinel σ R))
    (hs : Inv (Verify.instOf m).store) (h1 : pix.OneShot) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P m wix pix pol ppol ⊆ R :=
  mixedRel_subset_of_AG hw ha hb ho fun t ht σ => traces_AG (hm σ) hs h1 t ht

/-- **Soundness over fixed environments**, for every writer policy. -/
theorem moduleMixedFixedRel_sound_of_gameSat {Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv (mixedISpec wix pol.sentinel ρ)
      (parseESpec pix ppol.sentinel ρ R))
    (hs : Inv (Verify.instOf m).store) (h1 : pix.OneShot) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedFixedRel P m wix pix pol ppol Envs ⊆ R :=
  mixedFixedRel_subset_of_AG hb ho fun ρ hρ t ht => traces_AG (hm ρ hρ) hs h1 t ht

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed
