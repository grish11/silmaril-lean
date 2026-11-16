module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Call

/-!
# Linked sessions: specification to IR, and reference to IR

* `sessSpec_rounds`: a `Linked2.SessSpec` session is a list of well-formed session rounds whose
  instance plays are one play of the importer's instance and whose component import calls are
  one `ExpRunT` of the exporter, its linked plays the session's IR play (`Linked2.sessMoves`);
* `linked2_sess_specToIR`: with `linked2_sessToIR` (#703), specification sessions from the
  instances' stores are plays of `l.toComp.den (impSem P)`;
* `linked2_sess_sound`: with `linked2_sess_refToSpec`, reference session behaviours are IR plays.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

local notation "IVal" => Silmaril.Wasm.Component.Val

theorem expRunT_append {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance} {s s₁ s₂ : Store Nat}
    {ds ds' : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h : Linked2.ExpRunT P l I s ds s₁) (h' : Linked2.ExpRunT P l I s₁ ds' s₂) :
    Linked2.ExpRunT P l I s (ds ++ ds') s₂ := by
  induction h with
  | nil => exact h'
  | ret w hw hr _ ih => exact .ret w hw hr (ih h')
  | trap w hw ht _ ih => exact .trap w hw ht (ih h')

theorem sessSpec_length {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    {u π u' π' : Store Nat} {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (h : Linked2.SessSpec P l Ie Ii u π calls outs u' π') :
    calls.length = outs.length := by
  induction h with
  | nil => rfl
  | round _ _ _ _ _ _ ih => simp only [List.length_cons, ih]

/-- **A specification session is a list of session rounds**, played one after another. -/
theorem sessSpec_rounds {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    {u π u' π' : Store Nat} {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (h : Linked2.SessSpec P l Ie Ii u π calls outs u' π') :
    ∃ L : List (Linked2.SessRound l Ii), (∀ d ∈ L, d.Ok) ∧
      Ii.Path P (.idle u) (L.flatMap Linked2.SessRound.instMoves) (.idle u') ∧
      Linked2.ExpRunT P l Ie π (L.flatMap fun d => d.dss.flatten) π' ∧
      L.flatMap Linked2.SessRound.linkMoves = Linked2.sessMoves l calls outs := by
  induction h with
  | nil u π => exact ⟨[], (fun _ h => nomatch h), .nil _, .nil _, rfl⟩
  | round d hok hpath hrun hans _ ih =>
    obtain ⟨L, hL, hp, hr, hm⟩ := ih
    refine ⟨d :: L, ?_, ?_, ?_, ?_⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | h
      · exact hok
      · exact hL d' h
    · rw [List.flatMap_cons]
      exact path_append hpath hp
    · rw [List.flatMap_cons]
      exact expRunT_append hrun hr
    · rw [List.flatMap_cons, hm]
      simp only [Linked2.SessRound.linkMoves, hans]
      rfl

/-- **Specification sessions are IR plays**: a `Linked2.SessSpec` session from the instances'
stores is a play of `l.toComp.den (impSem P)`. -/
theorem linked2_sess_specToIR {l : Linked2} (he : l.exp.Good) (hi : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {u' π' : Store Nat} (h : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) := by
  obtain ⟨L, hL, hp, hr, hm⟩ := sessSpec_rounds h
  rw [← hm]
  exact LinkedSessionIR.linked2_sessToIR P l he hi Ie hIe Ii hIi L hL _ hp _ hr

/-- **Reference sessions of a linked component are IR plays** (every profile and component
choice profile): under `Linked2.Adequate`, every resumable-session outcome list of `l.toRef`
for typed calls is the reference image of outcomes whose session play is a play of
`l.toComp.den (impSem P)`. -/
theorem linked2_sess_sound (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ Linked2.sessObs prof l impl h₀ calls) :
    ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
      Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) := by
  obtain ⟨Ie, Ii, outs, u', π', hIe, hIi, hspec, rfl⟩ :=
    linked2_sess_refToSpec P prof l hl impl h₀ calls ht ho
  exact ⟨outs, rfl, sessSpec_length hspec,
    linked2_sess_specToIR hl.expGood hl.impGood hIe hIi hspec⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
