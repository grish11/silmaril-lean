module

public import Silmaril.Wasm.Component.Reference.HAcceptTuple.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple.Sess

/-!
# A `tuple<u8, u8>` acceptor as an `HLinked2`: theorems

All proved, at every profile `P`. Proofs: `Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple.{Inst, Sess}`.

* `tupleL_adequate`: `tupleL` satisfies `HLinked2.Adequate`. The instance of `tupleCore` is
  computed by kernel evaluation of validation and instantiation. So the hypotheses of
  `HLinked2.sessAdequacy_full` are met by an acceptor of the `tuple<u8, u8>` shape.
* `tupleL_hostTyped`: the host `acceptG` (every call answered with no results) is typed.
* `tupleL_ir_session`: **an execution-backed IR play**. In the session `[run]` of
  `tupleL.toComp.den (impSem P)`, `run` makes the host call `accept(record [u8 104, u8 105])`,
  which is answered with no results, and then returns. The play is built from a Core 3.0 run of
  `run` (`i32.const 104; i32.const 105; call 0` up to the callout, then the return after the
  answer), from the `canon lower` of the call (`ImpRel`), and from `HLinked2.sess_specToIR`.
* `tupleL_hostRun`: the logging host of `acceptG` answers that call and logs
  `(0, [record [u8 104, u8 105]], [])`.

Not shown: that `run` makes no other host call, i.e. that `"hi"` is the only string accepted.
-/

public section

namespace Silmaril.Wasm.Component.Reference.HAcceptTuple

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- **`tupleL` satisfies the adequacy hypotheses** (proved). -/
theorem tupleL_adequate : tupleL.Adequate :=
  Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple.tupleL_adequate

/-- **`acceptG` is a typed host for `tupleL`** (proved). -/
theorem tupleL_hostTyped : tupleL.HostTyped acceptG :=
  Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple.tupleL_hostTyped

/-- **The IR play of the session `[run]`** (proved, every profile): `run` calls the host import
`accept` on `record [u8 104, u8 105]`, the call is answered with no results, and `run`
returns. -/
theorem tupleL_ir_session (P : Profile) :
    tupleL.sessMoves [(⟨0, by decide⟩, [])] [some []]
        [[⟨(⟨0, by decide⟩, .vals [.record [.u8 104, .u8 105]]), some (.vals [])⟩]] ∈
      tupleL.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple.tupleL_ir_session P

/-- **The logging host of `acceptG` answers the host call of `run` and logs it** (proved). -/
theorem tupleL_hostRun :
    HostRun (HLinked2.logG acceptG) ((), [])
      [(⟨(⟨0, by decide⟩, .vals [.record [.u8 104, .u8 105]]), some (.vals [])⟩ :
        Σ _ : (sigN tupleL.host.length).Op, Option Payload)]
      ((), [(⟨0⟩, [toRefVal (.record [.u8 104, .u8 105])], [])]) :=
  Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple.tupleL_hostRun

end Silmaril.Wasm.Component.Reference.HAcceptTuple
