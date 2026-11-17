module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Call
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# Diverging sessions of `HLinked2.toRef`: specification to reference

`hlinked2_divSpecToRef`: from the instantiation of `l.toRef` under the logging host
(`init_facts`), a specification session whose host calls are answered by `logG g` from
`(s₀, [])` is a resumable session of the reference machine ending between calls in the host
state and log of its `HostRun` (`sessH_fwd`); there, a round that never answers after its own
host calls is a quietly diverging call in the host state and log at the end of those host calls
(`linkDivH_fwd`). So `HLinked2.DivSpecToRef P prof l g` holds under `HLinked2.Adequate` and
`HLinked2.HostTyped g`, at every profile and component choice profile.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

/-- **Specification divergence of a linked session with host imports is reference divergence,
with the host log**: under `HLinked2.Adequate` and a typed host, `HLinked2.DivSpecToRef` holds at
every profile and component choice profile. -/
theorem hlinked2_divSpecToRef (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) : HLinked2.DivSpecToRef P prof l g := by
  intro s₀ calls j vs p hp
  obtain ⟨Ie, Ii, hs, u, π, st, hIe, hIi, hspec, hr, hd⟩ := hp
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (answerHostS P (HLinked2.logG g)) (s₀, []) hIe hIi
  have hHd := handles_answer (P := P) (prof := prof) (g := HLinked2.logG g) hl.impArity
    hl.impFloatFree hl.wireTy
  obtain ⟨cs', ιe', ιi', G', ST', hsr, R'⟩ := sessH_fwd (prof := prof)
    (impl := answerImplS (HLinked2.logG g)) hHd (HostTyped.logG hT) S₀ rfl hfs hspec _ _ _ _ []
    (s₀, []) 0 st R₀ hr
  rw [Nat.zero_add] at R'
  have hdiv := linkDivH_fwd (prof := prof) (impl := answerImplS (HLinked2.logG g)) (ST := ST')
    hHd (HostTyped.logG hT) S₀ rfl hfs R' hd
  refine ⟨_, ⟨0⟩, l.exportMap,
    calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId),
    readyCfgL cs' ιe' ιi' fs G' ST' st, ⟨l.host.length + l.exp.exports.length + j⟩, hmem,
    mapM_lookupH hl.impGood calls, exportMapH_lookup hl.impGood j, ?_, hdiv⟩
  rw [zip_callArgsH]
  exact hsr

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
