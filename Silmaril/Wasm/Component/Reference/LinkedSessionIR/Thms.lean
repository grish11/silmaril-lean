module

public import Silmaril.Wasm.Component.Reference.LinkedSessionIR.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Fixture

/-!
# The IR side of linked sessions: theorems

**Scope.** `Linked2` only: two components linked through the canonical ABI (an import-free
exporter answering the importer's imports). The general linked composition, and with it a
linked adequacy theorem for arbitrary component graphs, waits on the composition closure of
`DStrategy` (the H2 owner's part, asked on #207). The parser from bytes to these components
and F6 are pending.

* **Linked sessions, exporter traps continuing** (`Linked2.sessToIR : Linked2.SessToIR`): for
  every profile `P`, rounds of the importer's instance, one after another from its store, whose
  component import calls are answered by the exporter's specification with returned **and
  trapped** calls threading the exporter's Core store (`Linked2.ExpRunT`), are the linked plays of
  `l.toComp.den (impSem P)`, one after another. So the IR keeps the exporter instance's trap
  store across export calls of the linked component. The proof rests on `expRunT_rounds`
  (`Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Rounds`), which mirrors
  `expRun_rounds`: an `ExpRunT` from `s` to `s'` is a complete activation of the exporter's
  instance from `s` to `s'` and rounds through its export handlers.
* **A trapped import call** (`trapImport_path`, `impRel_trap`): a core instance whose export
  call runs to an import call answered by a trap answers the export call with a trap, at the
  store it reached (every instance and profile); and that core import call corresponds
  (`ImpRel`) to the component import call answered `none`. The lifted answer of the importer's
  round is then `none`.
* **The fixture** `linkedC` (`LinkedSession`; A's `set` writes `g := 1` then traps, B's `poke`
  and `peek` call A's `set` and `get`): for every profile, the linked IR plays
  `poke · trap · peek · 1` (`linkedC_ir_session`, the IR counterpart of the reference session
  `linkedC_session`), and `peek · 0` on a fresh instance (`linkedC_ir_peek_fresh`).

**Not claimed.** The converse (every finite play of `l.toComp.den (impSem P)` is such a
session) and with it the linked analogue of `Simple.sessAdequacy` (#676): the session plays of
`den` are exactly the reference session behaviours (`sessBehaviours` of `l.toRef`). What
remains for it:

* the read-back of plays of `l.toComp.den (impSem P)` through the composition (the second
  environment over the first, `cplay_comp_serve` in reverse) into importer rounds and an
  `ExpRunT` (as `sessRounds_of_den` does for `Simple`); this inverts the composition of two
  strategies, i.e. needs the decomposition of `Strategy.comp` plays that the `DStrategy`
  closure provides;
* the reference side: `SessCalls` of `l.toRef` read as importer rounds whose lowered import
  calls run the exporter's lifted functions in the shared core store with `resumeCfg` after a
  trap (`Linked2.sound` covers single calls, `RefToSpec` for sequences of linked calls is not
  done), and the converse specification-to-reference direction.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.{Rounds, Fixture}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- **The IR side of linked sessions, exporter traps continuing** (proved). -/
theorem Linked2.sessToIR : Linked2.SessToIR :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.linked2_sessToIR

section TrapImport

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (Thread toFlat?)

/-- **An import call answered by a trap traps the export call** (proved): a running export
call `f` that runs host-free to an import call `e`, answered by a trap, answers `f` with a trap,
at the store the import call was made in. -/
theorem trapImport_path {I : ScalarInstance} {P : Profile} {q : I.HState}
    {p : List (Silmaril.Games.Move I.E I.F)} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread}
    {h : Nat} {args : List Silmaril.Wasm.Execution.Core.Val} {e : I.E.Op}
    (hp : I.Path P q p (.running f s t)) (run : Reach P (s, t) (s', t'))
    (co : CalloutAt s' t' h args) (op : I.importOp? h args = some e) :
    I.Path P q (p ++ [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]) (.idle s') :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.trapImport_path hp run co op

/-- **A core import call answered by a trap** is the component import call on the lifted
arguments answered `none` (proved). -/
theorem impRel_trap {c : SimpleI} {I : ScalarInstance} {e : I.E.Op} {nm : String} {ft : FuncTy}
    (hk : c.imports[e.1.val]? = some (nm, ft)) {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs ft.params (e.2.1.filterMap toFlat?) = some ws) :
    ImpRel c I ⟨e, .trap⟩ [⟨(⟨e.1.val, (List.getElem?_eq_some_iff.mp hk).1⟩, .vals ws), none⟩] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.impRel_trap hk hws

end TrapImport

namespace LinkedSession

/-- **The linked IR persists the callee-trap store** (proved): for every profile, `poke`
answers a trap (A's `set` writes `g := 1` and traps inside B's import call) and the following
`peek` answers `1` (A's `get`, from the store `set`'s trap left). The IR counterpart of
`linkedC_session`. -/
theorem linkedC_ir_session (P : Profile) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [])) none),
      .inr (.ask (⟨1, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨1, by decide⟩, .vals [])) (some (.vals [.u32 1])))] :
      List (Silmaril.Games.Move linkedC.toComp.imports.sig
        (sigN linkedC.toComp.exports.length))) ∈
      linkedC.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.linkedC_ir_session P

/-- **`peek` on a fresh instance answers `0`** (proved), for every profile. -/
theorem linkedC_ir_peek_fresh (P : Profile) :
    ([.inr (.ask (⟨1, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨1, by decide⟩, .vals [])) (some (.vals [.u32 0])))] :
      List (Silmaril.Games.Move linkedC.toComp.imports.sig
        (sigN linkedC.toComp.exports.length))) ∈
      linkedC.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.linkedC_ir_peek_fresh P

end LinkedSession

end Silmaril.Wasm.Component.Reference
