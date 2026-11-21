module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Defs
public import Silmaril.Wasm.Logic.GameLink.Thms

/-!
# Proofs: the game link for stateful export specifications

`strategy_sag`: if an instance meets a stateful specification (`SGameSat P I Ii S`), every play of
its strategy from a store representing the ghost state `g` is assume/guarantee correct read from
`g` (`SAG Ii S g`). The proof is that of `Silmaril.Wasm.Logic.GameLink.strategy_sound` with the
invariant `Good g` indexed by the ghost state: an idle store represents `g`; a running or waiting
thread is safe for the postcondition of its export call, asked in a store representing `g`.

New proofs (no source), following `Silmaril.Proofs.Wasm.Logic.GameLink.Strategy`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream

open Silmaril.Games Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded (Thread decompose? resumeResult)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.GameLink
open Silmaril.Wasm.Game.HandleAccept.Mixed.Stream

variable {I : ScalarInstance} {P : Profile} {G : Type} {Ii : ISpec I.E} {S : SSpec I G}

/-- The postcondition of a run answering the export question `f` asked in store `s₀`. -/
abbrev sqPost (I : ScalarInstance) (S : SSpec I G) (f : I.F.Op) (s₀ : Store Nat) : Post Nat :=
  callPost {} [] ((sexportSpec I S f.1).post s₀ f.2.1)

/-- **The invariant**, indexed by the ghost state. -/
def Good (P : Profile) (I : ScalarInstance) (Ii : ISpec I.E) (S : SSpec I G) (g : G) :
    I.HState → Prop
  | .idle s => S.inv g s
  | .running f s t => ∃ s₀, S.inv g s₀ ∧
      ∀ n, Safe P (gameHost I Ii) (sqPost I S f s₀) n (t.config s)
  | .waiting f s t e => ∃ s₀, S.inv g s₀ ∧ ∀ v : I.E.Ar e, Ii.post e v → ∀ n,
      Safe P (gameHost I Ii) (sqPost I S f s₀) n
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

theorem initThread_safe (hm : SGameSat P I Ii S) {g : G} {s : Store Nat} (hs : S.inv g s)
    (f : I.F.Op) (n : Nat) :
    Safe P (gameHost I Ii) (sqPost I S f s) n ((I.initThread f).config s) := by
  obtain ⟨j, args, ht⟩ := f
  exact hm j n s args ⟨⟨g, hs⟩, ht⟩ {} [] _ trivial

theorem good_call {g : G} {f : I.F.Op} {s : Store Nat} {t : Thread} {k : Nat}
    {args : List Val} {e : I.E.Op} (hx : Good P I Ii S g (.running f s t))
    (callout : CalloutAt s t k args) (op : I.importOp? k args = some e) :
    Ii.pre e ∧ Good P I Ii S g (.waiting f s t e) := by
  obtain ⟨s₀, hg, h⟩ := hx
  obtain ⟨E, a, hd⟩ := callout
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, k, args) := by
    rw [config_store]
    exact hd
  have hpre : Ii.pre e := by
    have hspec := Silmaril.Wasm.Logic.Open.import_pre (h 1) hd'
    rw [config_store] at hspec
    exact import_pre_of_spec op hspec
  exact ⟨hpre, s₀, hg, fun v hv n =>
    (h (n + 1)).step_inv (resume_step hd (gameHost_answer op hpre hv))⟩

theorem final_answer {g : G} {f : I.F.Op} {s₀ s : Store Nat} {t : Thread} {r : Result}
    {v : I.F.Ar f} (hg : S.inv g s₀) (hsafe : Safe P (gameHost I Ii) (sqPost I S f s₀) 1 (t.config s))
    (final : ResultAt s t r) (answer : Answer.ofResult? (I.exports.get f.1) r = some v) :
    S.post g f v ∧ S.inv (S.next g f v) s := by
  have hcode : (t.config s).code = r.toAdmin := final
  have hc : t.config s = ⟨s, (t.config s).frame, r.toAdmin⟩ :=
    calc t.config s = ⟨(t.config s).store, (t.config s).frame, (t.config s).code⟩ := rfl
      _ = ⟨s, (t.config s).frame, r.toAdmin⟩ := by rw [config_store, hcode]
  have hsafe' : Safe P (gameHost I Ii) (sqPost I S f s₀) 1 ⟨s, (t.config s).frame, r.toAdmin⟩ :=
    hc ▸ hsafe
  have hpost := Silmaril.Wasm.Logic.Open.final_post hsafe'
  have hv : v.toResult = r := Answer.toResult_of_ofResult? answer
  obtain ⟨j, args, ht⟩ := f
  exact hpost g hg ht v (by rw [hv])

theorem good_silent {g : G} {x y : I.HState} (hs : I.DTrans P x none y)
    (hx : Good P I Ii S g x) : Good P I Ii S g y := by
  cases hs with
  | tau h =>
    obtain ⟨s₀, hg, hsafe⟩ := hx
    exact ⟨s₀, hg, fun n => (hsafe (n + 1)).step_inv (internal_step h)⟩

/-- Every run from a good state is assume/guarantee correct, read from its ghost state. -/
theorem run_sag (hm : SGameSat P I Ii S) {s : Store Nat} {x y : (I.dlts P s).State}
    {p : List (Move I.E I.F)} (hr : (I.dlts P s).Run x p y) :
    ∀ g, Good P I Ii S g x → SAG Ii S g p := by
  induction hr with
  | nil => exact fun _ _ => trivial
  | tau hs _ ih => exact fun g hx => ih g (good_silent hs hx)
  | vis hs _ ih =>
    intro g hx
    cases hs with
    | call s f => exact ih g ⟨s, hx, initThread_safe hm hx f⟩
    | ucall callout op =>
      exact ⟨(good_call hx callout op).1, ih g (good_call hx callout op).2⟩
    | uret v =>
      obtain ⟨s₀, hg, h⟩ := hx
      exact fun hv => ih g ⟨s₀, hg, h v hv⟩
    | oret final answer =>
      obtain ⟨s₀, hg, h⟩ := hx
      have hans := final_answer hg (h 1) final answer
      exact ⟨hans.1, ih _ hans.2⟩

/-- **The game link for stateful specifications**: every play of the strategy from a store
representing `g` is assume/guarantee correct read from `g`. -/
theorem strategy_sag (hm : SGameSat P I Ii S) {g : G} {s : Store Nat} (hs : S.inv g s)
    {p : List (Move I.E I.F)} (hp : p ∈ I.strategy P s) : SAG Ii S g p := by
  obtain ⟨y, hr⟩ := (ScalarInstance.denotes_dlts P s p).2 hp
  exact run_sag hm hr g hs

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
