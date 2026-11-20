module

public import Silmaril.Wasm.Component.DecoderBridge.ParamName.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sem.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Wire.Defs
public import Silmaril.Wasm.Component.InstTests.Defs
public import Silmaril.Wasm.Component.RefValid.Defs
import Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName

/-!
# A parameter name the host does not have: `Task.startAdequacy` is false

All proved; proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName`.

* `parse_paramName`: the IR reading of `paramname.wasm` is `startsComp`, the IR reading of
  `starts.wasm` (parameter names are dropped), so it has the IR run of `starts.wasm`
  (`InstTests.starts_inst`);
* `decodeRef_paramName`, `paramName_valid`, `paramName_inFrag`: the REF reading is the valid
  `paramNameRef`, in the fragment `InFrag`;
* `not_rootChecked_paramName`, `starts_rootChecked` (`Sem.Thms`): the root compatibility
  certificate `RootChecked` (`Sem.Defs`) rejects `paramNameRef` (the pre-check of the root import
  compares parameter names, `y` against the host's `x`) and accepts `startsRef`;
* `traps_of_not_rootChecked`, `not_instantiates_of_not_rootChecked`,
  `sessRunFrom_empty_of_not_rootChecked`: **outside the certificate** the reference machine's
  instantiation (logging host, `hostConfigX`) traps, **no** run finishes it (the trap is reached
  by a run of unique steps from the instantiation host event, and a trap locks the store down),
  and there is no session run;
* `paramName_traps`, `paramName_not_instantiates`: for `paramNameRef`;
* `not_startAdequacy`: **`Task.startAdequacy` is false.** `paramname.wasm` meets every hypothesis
  (both readings succeed, the REF reading is valid and in `InFrag`, the IR imports are `hostI`,
  the IR plays of `starts.wasm`), and the reference machine has no session run.

The corrected start goal is `Task.startAdequacyChecked` (`Sem.Defs`), with the certificate
`RootChecked` as a hypothesis. The fragment `MultiImpFrag` of `Task.startAdequacyFrag` excludes
this binary: its condition `rootShape` asks for the root import `f: func(x: u32)`, parameter
name included, and every component of the fragment passes the root checks
(`Multi.Thms.rootChecked_of_multiImpFrag`).
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.SingleThreaded (neverFail)

/-- **The IR reading of `paramname.wasm` is that of `starts.wasm`.** -/
theorem parse_paramName : Binary.parseComponent paramNameBytes = .ok startsComp :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.parse_paramName

/-- **The REF reading of `paramname.wasm`.** -/
theorem decodeRef_paramName : decodeRef paramNameBytes = .ok paramNameRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.decodeRef_paramName

/-- The REF reading is valid. -/
theorem paramName_valid : ∃ ct, Valid Features.p2 paramNameRef ct :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.paramName_valid

/-- The REF reading is in the fragment. -/
theorem paramName_inFrag : InFrag paramNameRef := by decide +kernel

/-- **The certificate rejects `paramname.wasm`.** -/
theorem not_rootChecked_paramName : ¬ RootChecked paramNameRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.not_rootChecked_paramName

/-- **Outside the certificate the reference instantiation traps.** -/
theorem traps_of_not_rootChecked {r : RefComponent} (h : ¬ RootChecked r) :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.traps_of_not_rootChecked h

/-- **Outside the certificate no reference run finishes the instantiation.** -/
theorem not_instantiates_of_not_rootChecked {r : RefComponent} (h : ¬ RootChecked r)
    (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) (inst : InstId)
    (es : List (String × FuncId)) :
    ¬ Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX r
      (importArgs hostI) M inst es :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.not_instantiates_of_not_rootChecked h
    M inst es

/-- **Outside the certificate the reference has no session run.** -/
theorem sessRunFrom_empty_of_not_rootChecked {r : RefComponent} (h : ¬ RootChecked r)
    (calls : List (String × List Value.Val))
    (p : List (Option (List Value.Val)) × (Unit × List HLinked2.HostEvent)) :
    p ∉ sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) calls :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.sessRunFrom_empty_of_not_rootChecked h
    calls p

/-- **The reference instantiation traps.** -/
theorem paramName_traps :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX paramNameRef (importArgs hostI) :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.paramName_traps

/-- **No reference run finishes the instantiation.** -/
theorem paramName_not_instantiates
    (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) (inst : InstId)
    (es : List (String × FuncId)) :
    ¬ Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX paramNameRef
      (importArgs hostI) M inst es :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.paramName_not_instantiates M inst es

/-- **`Task.startAdequacy` is false.** -/
theorem not_startAdequacy : ¬ Task.startAdequacy :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName.not_startAdequacy

end Silmaril.Wasm.Component.DecoderBridge
