module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Call

/-!
# Sessions of a linked component with an abstract exporter, read back from between calls

* `sessL_invB`: every resumable session (`SessCalls`) of typed calls from a configuration between
  calls (`ReadyB`, no waiting thread) is the reference image of a `LinkedG.SessSpec` session from
  its stores (`linkCall_invB` for each call, `resumeCfg` after a trap);
* `sessL_iffB`: with `sessL_fwdB` of `LinkedGRound`, the session outcomes from such a
  configuration are exactly the reference images of the specification sessions.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

section Sess

variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
  {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fs : List (CFuncInst (core3P P))}
  {jf : Nat → Nat}

/-- **Resumable sessions between calls are specification sessions.** -/
theorem sessL_invB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hBw : d.BwdF) (hRes : d.Resume) (hB : d.Bounded) :
    ∀ (calls : List (Fin lg.imp.exports.length × List IVal)) (m : Machine.Config (E3 P) σ)
      (s : lg.exp.St) (u : Store Nat) (k : Nat)
      (outs : List (Option (List Silmaril.Wasm.Component.Reference.Val))),
      ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k → m.store.waiting = [] →
      SimpleI.TypedCalls lg.imp calls →
      SessCalls prof (linkHost impl) m k (callArgsG lg jf calls) outs →
      ∃ (outs' : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
        LinkedG.SessSpec P lg Ii u s calls outs' u' s' ∧ outs = refOuts outs'
  | [], m, s, u, k, outs, _, _, _, hS => by
    cases hS
    exact ⟨[], u, s, .nil u s, rfl⟩
  | (j, vs) :: calls, m, s, u, k, outs, R, hwt, ht, hS => by
    have hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true := ht _ List.mem_cons_self
    have ht' : SimpleI.TypedCalls lg.imp calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    change SessCalls prof (linkHost impl) m k ((⟨jf j⟩, vs.map toRefVal) :: callArgsG lg jf calls)
      outs at hS
    cases hS with
    | ret hcall hS' =>
      obtain ⟨dr, u₁, s₁, o, rfl, rfl, hok, hpath, hexp, hans, hback⟩ :=
        linkCall_invB ST hFr hBw hRes hB R hwt j hvs hcall
      cases o with
      | none => exact absurd hback.1 (by simp)
      | some ws =>
        obtain ⟨hout, R₁, hw₁⟩ := hback
        cases hout
        obtain ⟨outs', u', s', hspec, rfl⟩ :=
          sessL_invB ST hFr hBw hRes hB calls _ s₁ u₁ (k + 1) _ R₁ (hw₁.trans hwt) ht' hS'
        exact ⟨some ws :: outs', u', s', .round dr hok hpath hexp hans hspec, rfl⟩
    | trap hcall hS' =>
      obtain ⟨dr, u₁, s₁, o, rfl, rfl, hok, hpath, hexp, hans, hback⟩ :=
        linkCall_invB ST hFr hBw hRes hB R hwt j hvs hcall
      cases o with
      | some ws => exact absurd hback.1 (by simp)
      | none =>
        obtain ⟨-, R₁⟩ := hback
        obtain ⟨outs', u', s', hspec, rfl⟩ :=
          sessL_invB ST hFr hBw hRes hB calls _ s₁ u₁ (k + 1) _ R₁ hwt ht' hS'
        exact ⟨none :: outs', u', s', .round dr hok hpath hexp hans hspec, rfl⟩

/-- **The session outcomes between calls are the specification sessions'**: from a
configuration between calls with no waiting thread, the resumable-session outcome lists of typed
calls are the reference images of the outcomes of the `LinkedG.SessSpec` sessions from its
stores. -/
theorem sessL_iffB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hFw : d.Fwd) (hBw : d.BwdF) (hRes : d.Resume) (hB : d.Bounded)
    {calls : List (Fin lg.imp.exports.length × List IVal)} (ht : SimpleI.TypedCalls lg.imp calls)
    {m : Machine.Config (E3 P) σ} {s : lg.exp.St} {u : Store Nat} {k : Nat}
    (R : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k) (hwt : m.store.waiting = [])
    (outs : List (Option (List Silmaril.Wasm.Component.Reference.Val))) :
    SessCalls prof (linkHost impl) m k (callArgsG lg jf calls) outs ↔
      ∃ (outs' : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
        LinkedG.SessSpec P lg Ii u s calls outs' u' s' ∧ outs = refOuts outs' := by
  constructor
  · exact sessL_invB ST hFr hBw hRes hB calls m s u k outs R hwt ht
  · rintro ⟨outs', u', s', hspec, rfl⟩
    exact sessL_fwdB ST hFr hFw hRes hB hspec m k R

end Sess

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
