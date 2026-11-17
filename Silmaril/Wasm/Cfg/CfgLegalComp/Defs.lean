module

public import Silmaril.Wasm.Cfg.CfgLegal.Defs
public import Silmaril.Wasm.Cfg.SessionCheck.Defs
public import Silmaril.Wasm.Abstract.NodeLegalComp.Defs

/-!
# Exact legality of component denotations: definitions

The legality of hidden import answers on component-level hidden interactions. A hidden
interaction of `c.denUD (core3SemD P)` (node composition `DStrategy.ext`, wiring `implsN`,
nested instances, exports) restricts, at each core node `m`, to a hidden interaction of the node
strategy `semOfSD m (instSession m.inst P m.inst.store)`: a `NodeLegalComp.NodeWit` with its
hidden instance play `a`. Legality is stated there, relative to the store at the importer point
(the importing instance's `.waiting` state), `NodeLegalComp.WitLegal`.

* `NodeHidLegal P m`: every hidden interaction of the node of `m` (at its instantiation store) has
  a hidden instance play legal at every importer point for the CFG domain `CfgInst.LegalRes`.
* `CompLegal P c`: every core node of `c`, nested components included (`SessionCheck.CompIn`),
  is `NodeHidLegal`: every hidden node interaction of every component-level hidden interaction is
  legal at every importer point.

Theorems in `Silmaril.Wasm.Cfg.CfgLegalComp.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgLegalComp

open Silmaril.Wasm.Abstract.NodeLegalComp (NodeWit WitLegal)
open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumInstance)

/-- **Every hidden interaction of the node of `m` is legal at every importer point.** -/
def NodeHidLegal (P : Numerics.Profile) (m : NumInstance) : Prop :=
  ∀ p u v a b, NodeWit P m m.inst.store p u v a b → WitLegal P CfgInst.LegalRes m m.inst.store a

/-- **Every hidden node interaction of the component is legal at every importer point.** -/
def CompLegal (P : Numerics.Profile) (c : Comp NumInstance) : Prop :=
  SessionCheck.CompIn (NodeHidLegal P) c

end Silmaril.Wasm.Cfg.CfgLegalComp
