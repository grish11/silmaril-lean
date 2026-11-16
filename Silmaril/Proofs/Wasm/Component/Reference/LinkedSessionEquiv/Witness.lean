module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Main
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Fixture

/-!
# A witness of the linked session equivalence

`linkedR` is `linkedC` with the exporter's component exports renamed (`put`, `got` for `set`,
`get`). The IR ignores export names, so the two linked denotations are the same strategy
(`den_linkedR`); by `linked2_sessEquiv_iff` the two reference components, which differ, have the
same resumable sessions.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.LinkedSession
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR (setGetS_good pokePeekI_good)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Numerics (Profile)

/-- **The renamed exporter has the same IR**: the linked denotations of `linkedR` and `linkedC`
are the same strategy. -/
theorem den_linkedR (P : Profile) :
    linkedR.toComp.den (impSem P) = linkedC.toComp.den (impSem P) := by
  have hE : expNode (impSem P) linkedR = expNode (impSem P) linkedC := by
    simp only [expNode, denU_ofSimple, denU_toComp]
    rfl
  unfold Comp.den
  rw [denU_toCompL, denU_toCompL]
  simp only [envL, hE]
  rfl

theorem putGotS_good : putGotS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [putGotS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨"set", rfl⟩
    · exact ⟨"get", rfl⟩⟩

theorem putGotS_inst : putGotS.Inst := ⟨setGetS_inst.inst, setGetS_inst.names⟩

theorem linkedR_wireTy : linkedR.WireTy := by
  refine ⟨rfl, fun k w hk => ?_⟩
  match k, hk with
  | 0, hk =>
    have hw : w = 0 := (Option.some.inj hk).symm
    subst hw
    exact ⟨_, rfl, rfl⟩
  | 1, hk =>
    have hw : w = 1 := (Option.some.inj hk).symm
    subst hw
    exact ⟨_, rfl, rfl⟩
  | _ + 2, hk => simp [linkedR] at hk

theorem linkedR_namesOk : linkedR.NamesOk := by
  refine ⟨fun x hx => ?_, linkedC_namesOk.imp⟩
  simp only [linkedR, putGotS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ne_tag_of_length 2 (by decide) (by decide)
  · exact ne_tag_of_length 2 (by decide) (by decide)

/-- **`linkedR` satisfies the adequacy hypotheses.** -/
theorem linkedR_adequate : linkedR.Adequate :=
  ⟨putGotS_good, putGotS_inst, pokePeekI_good, pokePeekI_inst, pokePeekI_arity,
    pokePeekI_floatFree, linkedR_wireTy, linkedR_namesOk, linkedC_wireNodup,
    ⟨linkedC_splitOk.exp, linkedC_splitOk.imp⟩⟩

/-- **`linkedC` and `linkedR` are session-equivalent on the reference machine.** -/
theorem linkedC_refSessEquiv (P : Profile) (prof : ProfileKind) :
    Linked2.RefSessEquiv P prof linkedC linkedR :=
  (linked2_sessEquiv_iff P prof linkedC_adequate linkedR_adequate).mpr
    ⟨rfl, by rw [den_linkedR]; rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv
