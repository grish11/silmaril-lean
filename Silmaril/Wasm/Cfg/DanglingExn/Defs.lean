module

public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Wasm.Cfg.CfgInst.Defs

@[expose] public section

/-!
# Dangling exception addresses: definitions

A host may answer an import call by `throw a` for any address `a`. When `a` names no exception
instance of the store (`Dangling s a`, `s.exns.length ≤ a`), Core 3.0 still reduces: the host
answer becomes `throwing a` (`REF.EXN_ADDR a; THROW_REF`), and every rule that reads the
exception instance (`throw_ref-handler-catch`, `-catch_ref`, `CatchMatches`, `Ref_ok/exn`) reads
`s.exns[a]?`, which is `none`. The native region semantics resolves handlers by
`Cfg.Region.Catches`, which reads the same `s.exns[a]?` through the same `CatchMatches`.

The definitions describe what both semantics do with a dangling exception:

* `Dangling s a`: `a` is not an address of an exception instance of `s`;
* `Catch.CatchesAll c`: the clause catches every exception (`catch_all`, `catch_all_ref`);
* `danglingCatch a cs`: the resolution of the clauses `cs` for a dangling exception `a`. Tagged
  clauses (`catch`, `catch_ref`) are skipped; the first `catch_all l` catches with no payload,
  the first `catch_all_ref l` catches and pushes `ref.exn a` itself; with neither the exception
  is rethrown (`none`);
* `handlerOut a r`: the code a handler around `throwing a` reduces to, for the resolution `r`:
  `vals us ++ [br l]`, or `throwing a` again;
* `danglingNext n a cs c`: the one Core step of `HANDLER_n{c :: cs} (throwing a)` for a dangling
  `a`: a tagged clause is dropped (`throw_ref-handler-next`), a catch-all clause branches;
* `cfgInstTripleU I`: the CFG instance triple at the unrestricted universal host
  `CfgInst.instHostU I` (every answer of the import type, dangling exceptions included), the same
  view as `CfgInst.cfgInstTripleL` without the legality restriction.

Theorems in `Silmaril.Wasm.Cfg.DanglingExn.Thms`.
-/

namespace Silmaril.Wasm.Cfg.DanglingExn

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **`a` is a dangling exception address of `s`**: it names no exception instance. -/
def Dangling (s : Store H) (a : Nat) : Prop := s.exns.length ≤ a

/-- A clause that catches every exception, whatever its tag. -/
def _root_.Silmaril.Wasm.Catch.CatchesAll : Catch → Prop
  | .catchAll _ | .catchAllRef _ => True
  | .catch_ _ _ | .catchRef _ _ => False

/-- **The handler resolution of a dangling exception `a`**: tagged clauses are skipped; the first
catch-all clause catches, `catch_all_ref` with the reference `ref.exn a` as its payload. -/
def danglingCatch (a : Nat) : List Catch → Option (List Val × LabelIdx)
  | [] => none
  | .catch_ _ _ :: cs | .catchRef _ _ :: cs => danglingCatch a cs
  | .catchAll l :: _ => some ([], l)
  | .catchAllRef l :: _ => some ([.ref (.exn a)], l)

/-- The code a handler around `throwing a` leaves, for the resolution `r`: the payload and a
branch, or the exception rethrown. -/
def handlerOut (a : Nat) : Option (List Val × LabelIdx) → List Admin
  | some (us, l) => vals us ++ [.plain (.br l)]
  | none => throwing a

/-- The one Core step of `HANDLER_n{c :: cs} (throwing a)` for a dangling `a`. -/
def danglingNext (n a : Nat) (cs : List Catch) : Catch → List Admin
  | .catch_ _ _ | .catchRef _ _ => [.handler n cs (throwing a)]
  | .catchAll l => [.plain (.br l)]
  | .catchAllRef l => [.ref (.exn a), .plain (.br l)]

/-- **The CFG instance triple with every host answer**: the view, on the import signature of
`I`, of the self-contained CFG session triple openly restricted to the unrestricted universal
host `instHostU I`, whose exceptions may be dangling. -/
noncomputable def cfgInstTripleU (I : Game.ScalarInstance) :
    Silmaril.Games.Abstract.ObsTriple I.E (Store Nat) I.F.Op
      (Abstract.InstSession.Res I.exports ⊕ PUnit) :=
  Abstract.NodeBridge.viewTriple I
    (CfgInst.openRestrict (Abstract.coreHostRel (CfgInst.instHostU I)) CfgClosure.cfgSessionTripleC)

end Silmaril.Wasm.Cfg.DanglingExn
