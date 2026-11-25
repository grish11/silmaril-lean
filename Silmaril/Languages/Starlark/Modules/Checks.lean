module

import Silmaril.Languages.Starlark.Modules.Thms
meta import Silmaril.Languages.Starlark.Modules.Defs
meta import Silmaril.Languages.Starlark.Functions.Arguments.Defs
meta import Silmaril.Languages.Starlark.Functions.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Modules

open Functions (Program)
open Lists (State)

private def integer (n : Int) : Lists.Expr := .scalar (.int n)
private def read (binding : Binding) : Lists.Expr := .read (.bound binding)

private def program : Program := #[
  ⟨{}, [], [⟨globalSlot "x", globalSlot "x"⟩], .total (.ret (read (globalSlot "x")))⟩,
  ⟨{}, [], [⟨globalSlot "_secret", globalSlot "_secret"⟩],
    .total (.atomic (.eval (.append (read (globalSlot "_secret")) (integer 1))))⟩]

private def provider : Source := ⟨["read", "x", "_secret", "bump"], [],
  [.exec (.define "read" 0), .exec (.atomic (.assign (globalSlot "x") (integer 7))),
   .exec (.atomic (.assign (globalSlot "_secret") (.list .empty))), .exec (.define "bump" 1)]⟩

private def consumer : Source := ⟨["x", "out"], [],
  [.load "provider" [⟨"read", "get"⟩], .exec (.atomic (.assign (globalSlot "x") (integer 99))),
   .exec (.call (some (globalSlot "out")) (read (fileSlot "get")) {})]⟩

private def host (published : Published) : Catalog :=
  fun label => if label = "provider" then some published else none

private def good : Bool :=
  let caller : State := { iterators := [99] }
  match initializeModule program (fun _ => none) provider caller with
  | .error .. => false
  | .ok a state =>
    (List.lookup "_secret" a.exports).isNone && state.iterators == [99] &&
    match initializeModule program (host a) consumer state with
    | .error .. => false
    | .ok b state =>
      decide (List.lookup "out" b.exports = some (.scalar (.int 7))) &&
      decide (List.lookup "x" b.exports = some (.scalar (.int 99))) &&
      (List.lookup "get" b.exports).isNone && state.iterators == [99]

#guard good

-- The provider's private list is frozen by publication and a later import
-- of its public function observes that freeze.
#guard
  match initializeModule program (fun _ => none) provider {} with
  | .error .. => false
  | .ok published state =>
    let code : Source := ⟨[], [], [.load "provider" [⟨"bump", "go"⟩],
      .exec (.call none (read (fileSlot "go")) {})]⟩
    match initializeModule program (host published) code state with
    | .error (.runtime (.frozen _)) _ => true
    | _ => false

#guard
  match initializeModule program (fun _ => none)
    ⟨[], [], [.load "provider" [⟨"_secret", "local"⟩]]⟩ {} with
  | .error (.privateImport "_secret") state => state.heap.isEmpty
  | _ => false

#guard
  match initializeModule program (fun _ => none)
    ⟨["x"], [], [.load "provider" [⟨"read", "x"⟩]]⟩ {} with
  | .error (.bindingCollision "x") state => state.heap.isEmpty
  | _ => false

#guard
  match initializeModule program (fun _ => some ⟨[]⟩)
    ⟨[], [], [.load "provider" [⟨"unknown", "local"⟩]]⟩ {} with
  | .error (.missingExport "provider" "unknown") state => (state.slots (fileSlot "local")).isNone
  | _ => false

#guard
  match initializeModule program (fun _ => none)
    ⟨[], [], [.load "missing" [⟨"read", "local"⟩]]⟩ {} with
  | .error (.unavailableModule "missing") state => (state.slots (fileSlot "local")).isNone
  | _ => false

-- A failed initializer preserves the effects before the error without freezing
-- or exporting the partially initialized module.
#guard
  let desc : Source := ⟨["xs"], [],
    [.exec (.atomic (.assign (globalSlot "xs") (.list .empty))),
     .exec (.atomic (.eval (.append (read (globalSlot "xs")) (integer 4)))),
     .exec (.atomic (.eval (.index (read (globalSlot "xs")) (integer 3))))]⟩
  match initializeModule program (fun _ => none) desc {} with
  | .error (.runtime (.indexRange 3 1)) state =>
    decide (state.heap[1]? = some ⟨.list [.scalar (.int 4)], false⟩) &&
      (state.slots (globalSlot "xs")).isNone
  | _ => false

end Silmaril.Languages.Starlark.Modules
