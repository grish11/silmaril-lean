module

public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Component.Conformance.ToRef.Defs

/-!
# The two readings of a component binary: what they share

A component binary is read in two ways in this library:

* **IR reading**, `Binary.parseComponent bytes : Except String (Comp Binary.CoreMod)`:
  the verified component grammar `Binary.parse : ByteArray → Except _ Binary.Ast`, then
  `Binary.lower : Binary.Ast → Except String (Comp Binary.CoreMod)` (`Binary.Lower.Defs`), a
  state-passing pass over the sections. Each embedded core module is read by
  `Binary.Lower.coreMod`, which runs the core decoder `Silmaril.Wasm.Binary.Core.decode?` and
  keeps the bytes and the function interface (`Binary.CoreMod`); each core `instantiate` becomes
  an IR node `.core m wiring`, the wiring resolved by name through the argument instances.
* **REF reading**, `Conformance.decodeRef bytes : Except String Core3Component`: the same
  grammar `Binary.parse`, then `Conformance.toRef : Binary.Ast → Except String Core3Component`
  (`Conformance.ToRef.Defs`), a section-by-section transcription into the reference syntax.
  Each embedded core module becomes `.coreModule m` with `m` from the same core decoder
  `decode?`; each core `instantiate m args` is kept as `.coreInstance (.instantiate m args)`.

So the two readings share the parser and the core decoder; they differ in `lower` and `toRef`.
This module names the parts of the shared AST and of each output that the bridge theorems
(`DecoderBridge.Thms`) relate:

* `modBytes ss`, `instExprs ss`: the bytes of the top-level core module sections and the
  top-level core instantiations `(module index, arguments)` of a section list, in order;
* `noModuleSort ss`: no top-level import, alias or export of the core module sort (the only
  other ways an entry enters the core module index space; `lower` rejects all three);
* `coreModSpace r`: the core module index space of a reference component, in order: a
  definition `.coreModule m` gives `some m`; an import, alias or export of the core module
  sort gives `none` (not a module definition of this component);
* `refInsts r`: the core instantiations `(module index, arguments)` of a reference component;
* `Rel c r`: the **instantiation correspondence**: the IR nodes of `c` and the core
  instantiations of `r` are in one-to-one order-preserving correspondence, and each IR node
  is `.core m w` where the reference module at the instantiation's index is a module
  definition `ref` with `decode? m.bytes = some ref`.

`Rel` says nothing about the IR wiring programs against the reference's instantiation
arguments, about canonical definitions, imports or exports; `DecoderBridge.Wire` relates them on
a decidable fragment.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component

/-- A core instantiation `(module index, arguments)`. -/
abbrev InstExpr : Type := Nat × List (String × Nat)

/-- The bytes of the top-level core module sections, in order. -/
def modBytes : List Binary.Section → List ByteArray
  | [] => []
  | .coreModule bs :: ss => bs :: modBytes ss
  | _ :: ss => modBytes ss

/-- The core instantiation of a core instance expression, if it is one. -/
def instExpr? : Binary.CoreInstanceExpr → Option InstExpr
  | .instantiate m args => some (m, args)
  | .exports _ => none

/-- The top-level core instantiations of a section list, in order. -/
def instExprs : List Binary.Section → List InstExpr
  | [] => []
  | .coreInstances xs :: ss => xs.filterMap instExpr? ++ instExprs ss
  | _ :: ss => instExprs ss

/-- A section adds no import, alias or export entry to the core module index space. -/
def sectionNoModuleSort : Binary.Section → Bool
  | .imports xs => xs.all fun i => match i.desc with | .coreModule _ => false | _ => true
  | .aliases xs => xs.all fun a => a.sort != .core .module
  | .exports xs => xs.all fun e => e.item.sort != .core .module
  | _ => true

/-- No section adds an import, alias or export entry to the core module index space. -/
def noModuleSort (ss : List Binary.Section) : Bool := ss.all sectionNoModuleSort

/-- The sort of the entry a reference alias defines. -/
def aliasSort : Syntax.Alias → Syntax.Sort_
  | .export_ _ _ s => s
  | .coreExport _ _ s => .core s
  | .outer _ _ s => s

/-- The core module index space of a reference component, in definition order: a module
definition gives `some m`; an import, alias or export of the core module sort gives `none`. -/
def coreModSpace {M : Type} : List (Syntax.Definition M) → List (Option M)
  | [] => []
  | .coreModule m :: ds => some m :: coreModSpace ds
  | .import_ _ (.coreModule _) :: ds => none :: coreModSpace ds
  | .alias a :: ds =>
    (if aliasSort a = .core .module_ then [none] else []) ++ coreModSpace ds
  | .export_ _ si _ :: ds =>
    (if si.sort = .core .module_ then [none] else []) ++ coreModSpace ds
  | _ :: ds => coreModSpace ds

/-- The core instantiations of a reference component, in definition order. -/
def refInsts {M : Type} : List (Syntax.Definition M) → List InstExpr
  | [] => []
  | .coreInstance (.instantiate m args) :: ds => (m, args) :: refInsts ds
  | _ :: ds => refInsts ds

/-- An IR node corresponds to a reference core instantiation: it is a core node over a module
whose bytes the core decoder reads as the module definition at the instantiation's index. -/
def NodeRel (space : List (Option Silmaril.Wasm.Module)) (n : Node Binary.CoreMod)
    (e : InstExpr) : Prop :=
  ∃ m w ref, n = .core m w ∧ space[e.1]? = some (some ref) ∧
    Silmaril.Wasm.Binary.Core.decode? m.bytes = some ref

/-- **The instantiation correspondence** between an IR component and a reference component. -/
def Rel (c : Comp Binary.CoreMod) (r : Conformance.RefComponent) : Prop :=
  List.Forall₂ (NodeRel (coreModSpace r)) c.nodes (refInsts r)

end Silmaril.Wasm.Component.DecoderBridge
