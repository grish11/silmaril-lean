module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch.Defs
public import Silmaril.Wasm.Logic.GameLink.Thms
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost

/-!
# Proofs: the game link for ghost import specifications

`strategy_gag`: if an instance meets a ghost import specification (`GhostGameSat P I Gi Inv`),
every play of its strategy from a store `s` with `Inv g s` is assume/guarantee correct read from
`g` (`GAG Gi g`). The proof follows `Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Link`
(itself `Silmaril.Wasm.Logic.GameLink.strategy_sound`), with the hidden states of the instance
related to the configurations of the specification world `gConfig g c` (host code `(k, g)`):

* a host-free step is a host-free step of the relabelled configuration (`Step.mapH`);
* at a callout the relabelled configuration is at the redex with host code `(k, g)`
  (`gDecompose`), so the precondition `Gi.pre g e` holds (the ghost is read back from the store,
  `gStore_inj`);
* an answer `v` meeting `Gi.post` is a step of `ghostHost` to the relabelled resumed
  configuration, with the ghost moved by `ask` and `next`;
* an export answer is read off a final configuration (`Open.final_post`), which ends in a store
  `gStore g s` with `Inv g s`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch

open Silmaril.Games Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded (Thread decompose? resumeResult)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.GameLink (config_store resume_config)
open Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch
open Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost (gStore gConfig ghostH)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost (gStore_inj gDecompose)
open Silmaril.Proofs.Wasm.Component.Reference (Config.mapH Step.mapH invoke_mapH)

variable {I : ScalarInstance} {P : Profile} {G : Type} {Gi : GISpec I.E G}
  {Inv : G → Store Nat → Prop}

/-- The postcondition of an export run. -/
abbrev gqPost (Inv : G → Store Nat → Prop) : Post (Nat × G) :=
  callPost {} [] fun s' _ => ∀ g sR, s' = gStore g sR → Inv g sR

/-- **The invariant**, indexed by the ghost state. -/
def Good (P : Profile) (I : ScalarInstance) (Gi : GISpec I.E G) (Inv : G → Store Nat → Prop)
    (g : G) : I.HState → Prop
  | .idle s => Inv g s
  | .running _ s t => ∀ n, Safe P (ghostHost I Gi) (gqPost Inv) n (gConfig g (t.config s))
  | .waiting _ s t e => (∃ g₀, g = Gi.ask g₀ e ∧ Gi.pre g₀ e) ∧ ∀ v : I.E.Ar e, Gi.post g e v →
      ∀ n, Safe P (ghostHost I Gi) (gqPost Inv) n
        (gConfig (Gi.next g e v)
          ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s))

theorem gConfig_store (g : G) (s : Store Nat) (t : Thread) :
    (gConfig g (t.config s)).store = gStore g s := by
  show Silmaril.Proofs.Wasm.Component.Reference.Store.mapH (ghostH g) (t.config s).store = _
  rw [config_store]
  rfl

theorem initThread_safe (hm : GhostGameSat P I Gi Inv) {g : G} {s : Store Nat} (hs : Inv g s)
    (f : I.F.Op) (n : Nat) :
    Safe P (ghostHost I Gi) (gqPost Inv) n (gConfig g ((I.initThread f).config s)) := by
  obtain ⟨j, args, ht⟩ := f
  have he : gConfig g ((I.initThread ⟨j, ⟨args, ht⟩⟩).config s) =
      invoke (gStore g s) (I.addr j) args :=
    invoke_mapH (ghostH g) s (I.addr j) args
  rw [he]
  exact hm j n (gStore g s) args ⟨g, s, rfl, hs, ht⟩ {} [] _ trivial

theorem good_silent {g : G} {x y : I.HState} (hs : I.DTrans P x none y)
    (hx : Good P I Gi Inv g x) : Good P I Gi Inv g y := by
  cases hs with
  | @tau f s s' t t' h =>
    obtain ⟨f', code', ht', hst⟩ := h
    have ht'' : t' = .active f' code' := ht'
    subst ht''
    intro n
    have hst' := Step.mapH (ghostH g) hst
    exact (hx (n + 1)).step_inv (Step.of_noHost _ hst')

theorem good_call {g : G} {f : I.F.Op} {s : Store Nat} {t : Thread} {k : Nat}
    {args : List Val} {e : I.E.Op} (hx : Good P I Gi Inv g (.running f s t))
    (callout : CalloutAt s t k args) (op : I.importOp? k args = some e) :
    Gi.pre g e ∧ Good P I Gi Inv (Gi.ask g e) (.waiting f s t e) := by
  obtain ⟨E, a, hd⟩ := callout
  have hd' : decompose? (gConfig g (t.config s)).store (gConfig g (t.config s)).code =
      some (E, a, (k, g), args) := by
    rw [gConfig_store]
    exact gDecompose (g := g) hd
  obtain ⟨S, hS, hpre⟩ := Silmaril.Wasm.Logic.Open.import_pre (hx 1) hd'
  obtain rfl : S = ghostImportSpec I Gi k := (Option.some.inj hS).symm
  rw [gConfig_store] at hpre
  obtain ⟨g', sR, hgs, e', hop', hpre'⟩ := hpre
  obtain ⟨fi, yy, ps, rs, hf, hc, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  obtain ⟨rfl, rfl⟩ := gStore_inj hgs hf hc
  obtain rfl : e = e' := Option.some.inj (op.symm.trans hop')
  refine ⟨hpre', ⟨g, rfl, hpre'⟩, fun v hv n => ?_⟩
  have hhost : ghostHost I Gi (k, g) (gConfig g (t.config s)).store args
      (.returned (gStore (Gi.next (Gi.ask g e) e v) s)
        (Answer.toResult (ft := I.imports.get e.1) v)) := by
    rw [gConfig_store]
    refine ⟨ghostImportSpec I Gi k, rfl, ⟨g, s, rfl, e, op, hpre'⟩, g, s, rfl, fun e'' hop'' => ?_⟩
    obtain rfl : e'' = e := Option.some.inj (hop''.symm.trans op)
    exact ⟨v, hv, rfl, rfl⟩
  have hst := Silmaril.Wasm.Logic.Open.redex_step_ret (P := P) hd' hhost
  have hres : (⟨gStore (Gi.next (Gi.ask g e) e v) s, (gConfig g (t.config s)).frame,
      E.fill (Answer.toResult (ft := I.imports.get e.1) v).toAdmin⟩ : Config (Nat × G)) =
      gConfig (Gi.next (Gi.ask g e) e v)
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s) := by
    rw [resume_config hd]
    rfl
  rw [hres] at hst
  exact (hx (n + 1)).step_inv hst

theorem final_inv {g : G} {s : Store Nat} {t : Thread} {r : Result}
    (hsafe : Safe P (ghostHost I Gi) (gqPost Inv) 1 (gConfig g (t.config s)))
    (final : ResultAt s t r) : Inv g s := by
  have hcode : (gConfig g (t.config s)).code = r.toAdmin := final
  have hc : gConfig g (t.config s) =
      ⟨gStore g s, (gConfig g (t.config s)).frame, r.toAdmin⟩ := by
    calc gConfig g (t.config s) = ⟨(gConfig g (t.config s)).store,
          (gConfig g (t.config s)).frame, (gConfig g (t.config s)).code⟩ := rfl
      _ = _ := by rw [gConfig_store, hcode]
  rw [hc] at hsafe
  exact Silmaril.Wasm.Logic.Open.final_post hsafe g s rfl

/-- Every run from a good state is assume/guarantee correct, read from its ghost state. -/
theorem run_gag (hm : GhostGameSat P I Gi Inv) {s : Store Nat} {x y : (I.dlts P s).State}
    {p : List (Move I.E I.F)} (hr : (I.dlts P s).Run x p y) :
    ∀ g, Good P I Gi Inv g x → GAG Gi g p := by
  induction hr with
  | nil => exact fun _ _ => trivial
  | tau hs _ ih => exact fun g hx => ih g (good_silent hs hx)
  | vis hs _ ih =>
    intro g hx
    cases hs with
    | call s f => exact ih g (initThread_safe hm hx f)
    | ucall callout op =>
      exact ⟨(good_call hx callout op).1, ih _ (good_call hx callout op).2⟩
    | uret v =>
      obtain ⟨hpre, h⟩ := hx
      exact ⟨hpre, fun hv => ih _ (h v hv)⟩
    | oret final answer =>
      exact ih g (final_inv (hx 1) final)

/-- **The game link for ghost import specifications.** -/
theorem strategy_gag (hm : GhostGameSat P I Gi Inv) {g : G} {s : Store Nat} (hs : Inv g s)
    {p : List (Move I.E I.F)} (hp : p ∈ I.strategy P s) : GAG Gi g p := by
  obtain ⟨y, hr⟩ := (ScalarInstance.denotes_dlts P s p).2 hp
  exact run_gag hm hr g hs

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch
