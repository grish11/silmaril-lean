module

public import Silmaril.Wasm.Abstract.XRecursionP.Defs

/-!
# Audit controls (not an API)

Adversarial positive controls for the CFG-closure dependency audit
(`Silmaril.Proofs.Wasm.Cfg.CfgClosureAudit`), declared in a module of **another topic**
(`Wasm.Abstract`) so that the audit is exercised across module and topic boundaries. Both hide
the native closed oracle `XRecursionP.closedCallXP`:

* `opaqueAlias`: an `opaque` constant whose value is the native oracle;
* `hiddenAlias`: a definition whose body is not exposed to importing modules (no `@[expose]`),
  so that an importer sees no body.

The audit must reject definitions using either. Nothing else may use them.
-/

namespace Silmaril.Wasm.Abstract.AuditControl

/-- **Audit control**: an `opaque` alias of the native closed oracle. -/
public opaque opaqueAlias : CallRel Nat := XRecursionP.closedCallXP

/-- **Audit control**: an alias of the native closed oracle whose body importers do not see. -/
public def hiddenAlias : CallRel Nat := XRecursionP.closedCallXP

end Silmaril.Wasm.Abstract.AuditControl
