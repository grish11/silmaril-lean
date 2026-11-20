module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Thms
public import Silmaril.Semantics.Accept.Mixed.Chunk.Thms

/-!
# Proofs: the chunk assume/guarantee bridge for instance plays

* `ChunkRetFrom ppol σ R b t`: the returns of `t` related in `σ` along the trace, read from the
  chunk buffer `b` (moved by `chunkStep` at every parsing event); `chunkRetFrom_at`: read at a
  decomposition `t = u ++ .p e :: v`, from every parsing state whose buffer is
  `chunkFold b (parseEvents u)`;
* `sag_chunkRet`: a play assume/guarantee correct for `chunkSSpec` from the ghost `g`, whose
  decoded writes agree with `σ`, has its returns related along the trace from `g`;
* `moduleMixedRel_sound_of_chunkSat`: with `strategy_sag` and the assume/guarantee law along the
  chunk buffer (`Silmaril.Accept.Mixed.mixedRel_subset_of_chunkAG`), a module meeting `chunkSSpec`
  in every environment, from a store representing the empty buffer, has its mixed relation in
  `R`; `moduleMixedFixedRel_sound_of_chunkSat`: the same over fixed environments `Envs`
  (`Silmaril.Accept.Mixed.mixedFixedRel_subset_of_chunkAG`), for every writer policy.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
open Silmaril.Wasm.Logic.Strategy (ISpec)

variable {Op V H X : Type}

/-- **The returns of a trace, read from the chunk buffer `b`.** -/
def ChunkRetFrom (ppol : PPolicy H) (σ : Env H X) (R : Set (List V × X)) :
    List V → List (MEv Op V H) → Prop
  | _, [] => True
  | b, .w _ :: t => ChunkRetFrom ppol σ R b t
  | b, .p e :: t =>
      (∀ ps w h ps', ps.buf = b → Returns ppol ps e w h ps' → h ≠ ppol.sentinel →
        ∀ x, σ h = some x → (w, x) ∈ R) ∧
      ChunkRetFrom ppol σ R (chunkStep b e) t

/-- `ChunkRetFrom` read at a decomposition. -/
theorem chunkRetFrom_at {ppol : PPolicy H} {σ : Env H X} {R : Set (List V × X)} :
    ∀ {b : List V} {u : List (MEv Op V H)} {e : PEv V H} {v : List (MEv Op V H)},
      ChunkRetFrom ppol σ R b (u ++ .p e :: v) →
      ∀ ps w h ps', ps.buf = chunkFold b (parseEvents u) →
        Returns ppol ps e w h ps' → h ≠ ppol.sentinel → ∀ x, σ h = some x → (w, x) ∈ R
  | _, [], _, _, hS => by simpa [ChunkRetFrom, parseEvents, chunkFold] using hS.1
  | b, .w _ :: u, _, _, hS => by
      simpa [parseEvents] using chunkRetFrom_at (b := b) (u := u) hS
  | b, .p e' :: u, _, _, hS => by
      intro ps w h ps' hps
      refine chunkRetFrom_at (b := chunkStep b e') (u := u) hS.2 ps w h ps' ?_
      rw [hps]
      rfl

theorem chunkRetFrom_w_append {ppol : PPolicy H} {σ : Env H X} {R : Set (List V × X)}
    {b : List V} (o : Option (WEv Op H)) (t : List (MEv Op V H)) :
    ChunkRetFrom ppol σ R b ((o.map .w).toList ++ t) ↔ ChunkRetFrom ppol σ R b t := by
  cases o <;> simp [ChunkRetFrom]

theorem writesAgree_of_append {W : Writer Op X} {s : Option H} {σ : Env H X}
    {l t : List (MEv Op V H)} (h : WritesAgree W s σ (l ++ t)) : WritesAgree W s σ t :=
  fun op args r hm => h op args r (List.mem_append_right _ hm)

variable {I : ScalarInstance} {wix : ConsWImports} {pix : ParseExports V}
  {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)} {R : Set (List V × SExp2 (BitVec 64))}

/-- **The ghost buffer is the chunk buffer**: an assume/guarantee correct play of the chunk
specification, with writes agreeing with `σ`, has its returns related along the trace. -/
theorem sag_chunkRet {σ : Env (BitVec 32) (SExp2 (BitVec 64))}
    {Inv : List V → Store Nat → Prop} :
    ∀ (p : List (Move I.E I.F)) (g : List V),
      SAG (mixedISpec (ts := I.imports) wix pol.sentinel σ) (chunkSSpec pix ppol σ R Inv) g p →
      WritesAgree (consW (BitVec 64)) pol.sentinel σ
        (mixedEvents (consWDecAsk wix) (consWDecAns wix) (parseDec pix) p) →
      ChunkRetFrom ppol σ R g
        (mixedEvents (consWDecAsk wix) (consWDecAns wix) (parseDec pix) p)
  | [], _, _, _ => trivial
  | .inl (.ask e) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      rw [chunkRetFrom_w_append]
      exact sag_chunkRet p g hS.2 (writesAgree_of_append hW)
  | .inl (.ans e v) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      rw [chunkRetFrom_w_append]
      refine sag_chunkRet p g (hS fun op args r hd => ?_) (writesAgree_of_append hW)
      exact hW op args r (List.mem_append_left _ (by simp [hd]))
  | .inr (.ask _) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      exact sag_chunkRet p g hS (writesAgree_of_append (l := [.w .enter]) hW)
  | .inr (.ans f v) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      obtain ⟨hpost, hS⟩ := hS
      have hW' := writesAgree_of_append hW
      rcases hd : parseDec pix f v with _ | e
      · have hn : chunkNext pix g f v = g := by simp [chunkNext, hd]
        simp only [Option.map_none, Option.toList_none, List.nil_append]
        have hS' : SAG (mixedISpec (ts := I.imports) wix pol.sentinel σ)
            (chunkSSpec pix ppol σ R Inv) g p := by
          have := hS
          simp only [chunkSSpec] at this
          rwa [hn] at this
        exact sag_chunkRet p g hS' hW'
      · have hn : chunkNext pix g f v = chunkStep g e := by simp [chunkNext, hd]
        simp only [Option.map_some, Option.toList_some, List.cons_append, List.nil_append]
        have hS' : SAG (mixedISpec (ts := I.imports) wix pol.sentinel σ)
            (chunkSSpec pix ppol σ R Inv) (chunkStep g e) p := by
          have := hS
          simp only [chunkSSpec] at this
          rwa [hn] at this
        exact ⟨hpost e hd, sag_chunkRet p _ hS' hW'⟩

variable {P : Numerics.Profile} {m : Module}

/-- **Soundness of a chunked parser module building its trees** (store semantics). -/
theorem moduleMixedRel_sound_of_chunkSat
    {Inv : Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    (hm : ∀ ρ, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (chunkSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ, Inv ρ [] (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P m wix pix pol ppol ⊆ R :=
  mixedRel_subset_of_chunkAG hw ha hb ho fun _ ⟨p, hp, ht⟩ σ hW u e v hd => by
    subst ht
    have hS := sag_chunkRet p [] (strategy_sag (hm σ) (hs σ) hp) hW
    rw [hd] at hS
    exact chunkRetFrom_at hS

/-- **Soundness of a chunked parser module over fixed environments**, for every writer policy. -/
theorem moduleMixedFixedRel_sound_of_chunkSat
    {Inv : Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    {Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))}
    (hm : ∀ ρ ∈ Envs, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (chunkSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ ∈ Envs, Inv ρ [] (Verify.instOf m).store) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedFixedRel P m wix pix pol ppol Envs ⊆ R :=
  mixedFixedRel_subset_of_chunkAG hb ho fun ρ hρ _ ⟨p, hp, ht⟩ hW u e v hd => by
    subst ht
    have hS := sag_chunkRet p [] (strategy_sag (hm ρ hρ) (hs ρ hρ) hp) hW
    rw [hd] at hS
    exact chunkRetFrom_at hS

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk
