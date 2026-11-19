module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Link
public import Silmaril.Semantics.Accept.Mixed.Stream.Thms

/-!
# Proofs: the streaming assume/guarantee bridge

`sag_streamRet`: a play that is assume/guarantee correct for the streaming parsing
specification read from the buffer `g`, whose decoded writes agree with `σ`, has its decoded
returns related in `σ` along the trace from `g` (`StreamRetFrom`): the ghost state of the play is
the append buffer of the parsing host. With `strategy_sag` and the streaming assume/guarantee
theorem of `Silmaril.Accept.Mixed`, `moduleMixedRel_sound_of_streamSat` and
`moduleMixedFixedRel_sound_of_streamSat` bound the relations of a module by `R`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
open Silmaril.Wasm.Logic.Strategy (ISpec)

variable {Op V H X : Type}

theorem streamRetFrom_w_append {ppol : PPolicy H} {σ : Env H X} {R : Set (List V × X)}
    {acc : List V} (o : Option (WEv Op H)) (t : List (MEv Op V H)) :
    StreamRetFrom ppol σ R acc ((o.map .w).toList ++ t) ↔ StreamRetFrom ppol σ R acc t := by
  cases o <;> simp [StreamRetFrom]

theorem writesAgree_of_append {W : Writer Op X} {s : Option H} {σ : Env H X}
    {l t : List (MEv Op V H)} (h : WritesAgree W s σ (l ++ t)) : WritesAgree W s σ t :=
  fun op args r hm => h op args r (List.mem_append_right _ hm)

variable {I : ScalarInstance} {wix : ConsWImports} {pix : ParseExports V}
  {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)} {R : Set (List V × SExp2 (BitVec 64))}

/-- **The ghost buffer is the parsing buffer**: an assume/guarantee correct play of the
streaming specification, with writes agreeing with `σ`, has its returns related along the
trace. -/
theorem sag_streamRet {σ : Env (BitVec 32) (SExp2 (BitVec 64))}
    {Inv : List V → Store Nat → Prop} :
    ∀ (p : List (Move I.E I.F)) (g : List V),
      SAG (mixedISpec (ts := I.imports) wix pol.sentinel σ) (streamSSpec pix ppol σ R Inv) g p →
      WritesAgree (consW (BitVec 64)) pol.sentinel σ
        (mixedEvents (consWDecAsk wix) (consWDecAns wix) (parseDec pix) p) →
      StreamRetFrom ppol σ R g
        (mixedEvents (consWDecAsk wix) (consWDecAns wix) (parseDec pix) p)
  | [], _, _, _ => trivial
  | .inl (.ask e) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      rw [streamRetFrom_w_append]
      exact sag_streamRet p g hS.2 (writesAgree_of_append hW)
  | .inl (.ans e v) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      rw [streamRetFrom_w_append]
      refine sag_streamRet p g (hS fun op args r hd => ?_) (writesAgree_of_append hW)
      exact hW op args r (List.mem_append_left _ (by simp [hd]))
  | .inr (.ask _) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      exact sag_streamRet p g hS (writesAgree_of_append (l := [.w .enter]) hW)
  | .inr (.ans f v) :: p, g, hS, hW => by
      simp only [mixedEvents] at hW ⊢
      obtain ⟨hpost, hS⟩ := hS
      have hW' := writesAgree_of_append hW
      rcases hd : parseDec pix f v with _ | e
      · have hn : streamNext pix ppol g f v = g := by simp [streamNext, hd]
        simp only [Option.map_none, Option.toList_none, List.nil_append]
        have hS' : SAG (mixedISpec (ts := I.imports) wix pol.sentinel σ)
            (streamSSpec pix ppol σ R Inv) g p := by
          have := hS
          simp only [streamSSpec] at this
          rwa [hn] at this
        exact sag_streamRet p g hS' hW'
      · have hn : streamNext pix ppol g f v = accStep ppol.doneClears g e := by
          simp [streamNext, hd]
        simp only [Option.map_some, Option.toList_some, List.cons_append, List.nil_append]
        have hS' : SAG (mixedISpec (ts := I.imports) wix pol.sentinel σ)
            (streamSSpec pix ppol σ R Inv) (accStep ppol.doneClears g e) p := by
          have := hS
          simp only [streamSSpec] at this
          rwa [hn] at this
        exact ⟨hpost e hd, sag_streamRet p _ hS' hW'⟩

variable {P : Numerics.Profile} {m : Module}

/-- **Soundness of a streaming parser module building its trees** (store semantics). -/
theorem moduleMixedRel_sound_of_streamSat
    {Inv : Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    (hm : ∀ ρ, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (streamSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ, Inv ρ [] (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P m wix pix pol ppol ⊆ R :=
  mixedRel_subset_of_streamAG hw ha hb ho fun _ ⟨p, hp, ht⟩ σ hW => by
    subst ht
    exact sag_streamRet p [] (strategy_sag (hm σ) (hs σ) hp) hW

/-- **Soundness over fixed environments**, for every writer policy. -/
theorem moduleMixedFixedRel_sound_of_streamSat
    {Inv : Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    {Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))}
    (hm : ∀ ρ ∈ Envs, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (streamSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ ∈ Envs, Inv ρ [] (Verify.instOf m).store) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedFixedRel P m wix pix pol ppol Envs ⊆ R :=
  mixedFixedRel_subset_of_streamAG hb ho fun ρ hρ _ ⟨p, hp, ht⟩ hW => by
    subst ht
    exact sag_streamRet p [] (strategy_sag (hm ρ hρ) (hs ρ hρ) hp) hW

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
