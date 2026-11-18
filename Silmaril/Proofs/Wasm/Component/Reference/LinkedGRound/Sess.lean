module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Call

/-!
# Sessions of a linked component with an abstract exporter, forward, between calls

`sessL_fwd` of `LinkedSessionFwd` for `LinkedG`: a `LinkedG.SessSpec` session from the stores of
a configuration between calls (`ReadyB`) is a resumable session of the reference machine
(`SessCalls`) from it, with the reference images of its outcomes (`linkCall_fwdB` for each
round; after a trap the session resumes from `resumeCfg`, where `ReadyB` holds by R5).

Not covered here: the configuration after the instantiation of `LinkedG.toRef` (R4 for the
exporter, the importer's instantiation after it), i.e. that `ReadyB` holds there.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- The reference calls of a session: export `j` at function id `jf j`, on the reference images
of the arguments. -/
def callArgsG (lg : LinkedG) (jf : Nat → Nat)
    (calls : List (Fin lg.imp.exports.length × List IVal)) :
    List (FuncId × List Silmaril.Wasm.Component.Reference.Val) :=
  calls.map fun q => (⟨jf q.1⟩, q.2.map toRefVal)

section Sess

variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
  {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fs : List (CFuncInst (core3P P))}
  {jf : Nat → Nat}

/-- **Specification sessions are resumable sessions of the machine between calls.** -/
theorem sessL_fwdB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hFw : d.Fwd) (hRes : d.Resume) (hB : d.Bounded)
    {calls : List (Fin lg.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {u : Store Nat} {s : lg.exp.St} {u' : Store Nat} {s' : lg.exp.St}
    (hspec : LinkedG.SessSpec P lg Ii u s calls outs u' s') :
    ∀ (m : Machine.Config (E3 P) σ) (k : Nat), ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k →
      SessCalls prof (linkHost impl) m k (callArgsG lg jf calls) (refOuts outs) := by
  induction hspec with
  | nil => intro m k _; exact .nil _ _
  | @round u u₁ u' s s₁ s' cs outs o dr hok hpath hexp hans _ ih =>
    intro m k R
    cases o with
    | some ws =>
      obtain ⟨m', hc, R'⟩ := linkCall_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB R dr
        hok hpath hexp hans
      exact .ret hc (ih _ _ R')
    | none =>
      obtain ⟨m', hc, R'⟩ := linkCall_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB R dr
        hok hpath hexp hans
      exact .trap hc (ih _ _ R')

end Sess

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
