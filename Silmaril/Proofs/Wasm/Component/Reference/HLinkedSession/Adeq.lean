module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.ReadBack
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.RefSess

/-!
# Linked components with host imports: finite session adequacy

The two directions between the specification and the IR (`hlinked2_sess_specToIR`,
`hlinked2_irToSpec`) together with the two between the specification and the reference machine
(`hlinked2_sessObs_eq`, `hlinked2_silentObs_eq`):

* `hlinked2_sessAdequacy`: under the logging host of a typed `g`, the reference session
  outcomes with their final host state and log are exactly the reference images of the outcome
  lists whose session play, host calls included, is an IR play, and whose host calls form a
  `HostRun (logG g)` from `(s₀, [])` to that host state and log;
* `hlinked2_silentAdequacy`: under the host that never answers, the same with the host calls
  all answered by a trap (`HostRun silentG`), in the initial host state.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "RVal" => Silmaril.Wasm.Component.Value.Val
local notation "IVal" => Silmaril.Wasm.Component.Val

/-- The IR plays of a session from the instances' stores are exactly the specification
sessions, for some instances of the exporter and the importer. -/
theorem hlinked2_spec_iff_ir (P : Profile) {l : HLinked2} (hl : l.Adequate)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    (outs : List (Option (List IVal)))
    (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))) :
    (∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (u' π' : Store Nat),
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π') ↔
    (calls.length = outs.length ∧ calls.length = hs.length ∧
      l.sessMoves calls outs hs ∈ l.toComp.den (impSem P)) := by
  constructor
  · rintro ⟨Ie, Ii, u', π', hIe, hIi, hS⟩
    obtain ⟨h₁, h₂⟩ := sessSpecH_length hS
    exact ⟨h₁, h₂, hlinked2_sess_specToIR hl.expGood hl.impGood hIe hIi hS⟩
  · rintro ⟨hlen, hlen', hm⟩
    obtain ⟨Ie, hIe⟩ := hl.expInst.inst
    obtain ⟨Ii, hIi⟩ := hl.impInst.inst
    obtain ⟨u', π', hS⟩ := hlinked2_irToSpec P l hl hIe hIi calls outs hs ht hlen hlen' hm
    exact ⟨Ie, Ii, u', π', hIe, hIi, hS⟩

/-- **Finite session adequacy with the host log.** -/
theorem hlinked2_sessAdequacy (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) :
    HLinked2.sessObs P prof l g s₀ calls =
      {p | ∃ (outs : List (Option (List IVal)))
        (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))),
        p.1 = refOuts outs ∧ calls.length = outs.length ∧ calls.length = hs.length ∧
        l.sessMoves calls outs hs ∈ l.toComp.den (impSem P) ∧
        HostRun (HLinked2.logG g) (s₀, []) hs.flatten p.2} := by
  rw [hlinked2_sessObs_eq P prof hl g hT s₀ calls ht]
  ext p
  constructor
  · rintro ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hS, hr, ho⟩
    obtain ⟨h₁, h₂, h₃⟩ :=
      (hlinked2_spec_iff_ir P hl calls ht outs hs).mp ⟨Ie, Ii, u', π', hIe, hIi, hS⟩
    exact ⟨outs, hs, ho, h₁, h₂, h₃, hr⟩
  · rintro ⟨outs, hs, ho, h₁, h₂, h₃, hr⟩
    obtain ⟨Ie, Ii, u', π', hIe, hIi, hS⟩ :=
      (hlinked2_spec_iff_ir P hl calls ht outs hs).mpr ⟨h₁, h₂, h₃⟩
    exact ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hS, hr, ho⟩

/-- **Finite session adequacy under a host that never answers.** -/
theorem hlinked2_silentAdequacy (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) :
    HLinked2.silentObs P prof l h₀ calls =
      {p | ∃ (outs : List (Option (List IVal)))
        (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))),
        p.1 = refOuts outs ∧ p.2 = h₀ ∧ calls.length = outs.length ∧
        calls.length = hs.length ∧ l.sessMoves calls outs hs ∈ l.toComp.den (impSem P) ∧
        HostRun HLinked2.silentG h₀ hs.flatten h₀} := by
  rw [hlinked2_silentObs_eq P prof hl h₀ calls ht]
  ext p
  constructor
  · rintro ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hS, hr, hs₀, ho⟩
    obtain ⟨h₁, h₂, h₃⟩ :=
      (hlinked2_spec_iff_ir P hl calls ht outs hs).mp ⟨Ie, Ii, u', π', hIe, hIi, hS⟩
    exact ⟨outs, hs, ho, hs₀, h₁, h₂, h₃, hr⟩
  · rintro ⟨outs, hs, ho, hs₀, h₁, h₂, h₃, hr⟩
    obtain ⟨Ie, Ii, u', π', hIe, hIi, hS⟩ :=
      (hlinked2_spec_iff_ir P hl calls ht outs hs).mpr ⟨h₁, h₂, h₃⟩
    exact ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hS, hr, hs₀, ho⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
