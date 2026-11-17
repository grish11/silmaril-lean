module

public import Silmaril.Wasm.Cfg.CfgClosure.Defs
public import Silmaril.Wasm.Cfg.CfgInst.Defs
public import Silmaril.Wasm.Cfg.DanglingExn.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Defs
public import Silmaril.Wasm.Cfg.CfgLegal.Defs
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-!
# Definition dependency audit of the CFG closure (H3, a build-time check)

Not a proof: an elaboration-time check that **fails the build**. It audits the definitions of the
self-contained CFG closure and the objects built from it:
- finished `cfgEvFunXPS`, pending `cfgEvPendXPS`, productive `cfgEvInfNXP`;
- divergent `cfgEvFunDXPSC`, `LDLcfgC`, `cfgAns`, `cfgFunDiv`;
- the triple `cfgSessionTripleC`;
- the instance triples `CfgInst.cfgInstTriple`, `CfgInst.cfgInstTripleL`;
- the session family `CfgInst.cfgInstSessionsL`;
- the unrestricted-host instance triple `DanglingExn.cfgInstTripleU`;
- the component semantics `CfgLegal.cfgSemD`.

## Scope of the dependency property

1. **Definitional dependencies.** The walk follows the constants used by the **types and bodies of
   definitions**, the types of inductive types, constructors and recursors, transitively. It does
   not follow the bodies of theorems: a proof does not change what a definition denotes (proof
   irrelevance), so the property is "the closure's *definitions* do not use a native closed or
   divergent object". On everything reached it checks that no **native closed or divergent object**
   is reached. These objects are:
   - anything in `XRecursionP`, `XDivergeP`, `XRecursion`, `XDiverge` or `Recursion`;
   - `CallXP.EvalOXP`;
   - the native open modules, closures and triples (`wasmHOpenXPS`, `wasmHOpenXP`, `wasmEvFunXPS`,
     `wasmEvFunXP`, `wasmEvFunDXP`, `wasmEvFunDXPS`, `wasmEvPendXPS`, `wasmEvInfNXP`,
     `sessionTripleXP`, `LogDivXP`, `InfLXP`, `LDLwXP`, `InfLwXP`).
2. **Fail closed on uninspectable constants.** A reached constant whose body the walk cannot
   inspect (an `opaque` constant, an axiom, a name missing from the environment, or, in a module,
   an imported definition whose body is not exposed) **fails** the audit, unless one of these holds:
   - **Its type is a proposition.** It is then a proof, and proofs are irrelevant to what a
     definition denotes.
   - **It is declared in a module of an external dependency** (not `Silmaril.*`, e.g. `Init`,
     `Std`, `Lean`, `Mathlib`). Such a module cannot import Silmaril, so its constants cannot
     depend on Silmaril's native objects.

   Opaque **data** or closures declared in Silmaril always fail.
3. **Axiom closure.** For every root, the axioms its whole closure depends on, proofs included
   (`Lean.collectAxioms`, as `#print axioms`), must be among `propext`, `Classical.choice` and
   `Quot.sound`. This is checked here directly, not inferred from `scripts/check-layout.sh`
   rejecting `axiom` declarations.

## Positive controls (the checks are effective)

- The scoped native instance `CfgSession.cfgSessionTriple` reaches `closedCallXP` and `FunDivXP`.
- **Adversarial:** `auditOpaqueRoot` uses `auditOpaqueAlias`, an `opaque` alias of the native
  oracle `closedCallXP`. The walk cannot see through it, and the audit must reject the root.
- The axiom check rejects `sorryAx`, the axiom behind `sorry`.

From the Wasm side, what is reached is the open logged relations `Abstract.EvalLXPS`/`ReachLXPS`
(every call an open entry, answered by nothing) and flow helpers.
-/

namespace Silmaril.Wasm.Cfg.Proofs.CfgClosureAudit

open Lean Elab Command

/-- The constants reachable from `roots` through definitions, and those whose body is not
available (axioms, opaque constants, missing names, unexposed imported bodies). -/
meta partial def reach (env : Environment) (roots : List Name) : NameSet × NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut unseen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.defnInfo d) =>
      stack := d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList ++ stack
    | some (.inductInfo i) => stack := i.type.getUsedConstants.toList ++ i.ctors ++ stack
    | some (.ctorInfo c) => stack := c.type.getUsedConstants.toList ++ stack
    | some (.recInfo r) => stack := r.type.getUsedConstants.toList ++ stack
    | some (.quotInfo q) => stack := q.type.getUsedConstants.toList ++ stack
    | some (.thmInfo _) => pure ()
    | some (.opaqueInfo o) =>
      unseen := unseen.insert n; stack := o.type.getUsedConstants.toList ++ stack
    | some (.axiomInfo a) =>
      unseen := unseen.insert n; stack := a.type.getUsedConstants.toList ++ stack
    | none => unseen := unseen.insert n
  return (seen, unseen)



meta def nativePrefixes : List Name :=
  [`Silmaril.Wasm.Abstract.XRecursionP, `Silmaril.Wasm.Abstract.XDivergeP,
    `Silmaril.Wasm.Abstract.XRecursion, `Silmaril.Wasm.Abstract.XDiverge,
    `Silmaril.Wasm.Abstract.Recursion]

meta def nativeNames : List Name :=
  [`Silmaril.Wasm.Abstract.CallXP.EvalOXP, `Silmaril.Wasm.Abstract.wasmHOpenXPS,
    `Silmaril.Wasm.Abstract.wasmHOpenXP, `Silmaril.Wasm.Abstract.wasmEvFunXPS,
    `Silmaril.Wasm.Abstract.wasmEvFunXP, `Silmaril.Wasm.Abstract.wasmEvFunDXP,
    `Silmaril.Wasm.Abstract.wasmEvFunDXPS, `Silmaril.Wasm.Abstract.wasmEvPendXPS,
    `Silmaril.Wasm.Abstract.wasmEvInfNXP, `Silmaril.Wasm.Abstract.sessionTripleXP,
    `Silmaril.Wasm.Abstract.LogDivXP, `Silmaril.Wasm.Abstract.InfLXP,
    `Silmaril.Wasm.Abstract.LDLwXP, `Silmaril.Wasm.Abstract.InfLwXP]

/-- Auxiliary proof constants (`_proof_i`), which are proofs. -/
meta def isProofAux (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_proof"
  | _ => false

meta def isNative (n : Name) : Bool :=
  nativePrefixes.any (·.isPrefixOf n) || nativeNames.contains n

/-- The module declaring `n` belongs to Silmaril (or `n` is missing: fail closed). -/
meta def inSilmaril (env : Environment) (n : Name) : Bool :=
  match Environment.getModuleIdxFor? env n with
  | some i => (`Silmaril).isPrefixOf ((Environment.header env).moduleNames[i.toNat]!)
  | none => true

/-- The violations of the audit from `r`: native objects reached, and uninspectable computational
constants declared in Silmaril. -/
meta def violations (r : Name) : CommandElabM (List MessageData) := do
  let env ← getEnv
  let (seen, unseen) := reach env [r]
  let mut out : List MessageData := []
  let bad := seen.toList.filter isNative
  unless bad.isEmpty do out := m!"{r} reaches native closed or divergent objects: {bad}" :: out
  let mut hid : List Name := []
  for n in unseen.toList do
    if isProofAux n then continue
    match env.find? n with
    | none => hid := n :: hid
    | some ci =>
      if (← liftTermElabM (Meta.isProp ci.type)) then continue
      if inSilmaril env n then hid := n :: hid
  unless hid.isEmpty do
    out := m!"{r}: uninspectable computational constants declared in Silmaril: {hid}" :: out
  return out

/-- The standard axioms. -/
meta def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The non-standard axioms the closure of `r` depends on, proofs included. -/
meta def badAxioms (r : Name) : CommandElabM (List Name) := do
  let ax ← liftCoreM (Lean.collectAxioms r)
  return ax.toList.filter (!stdAxioms.contains ·)

/-- **Adversarial control**: an `opaque` alias of the native closed oracle. -/
private opaque auditOpaqueAlias : Abstract.CallRel Nat := Abstract.XRecursionP.closedCallXP

/-- **Adversarial control**: a definition hiding the native oracle behind the opaque alias. -/
private def auditOpaqueRoot : Abstract.CallRel Nat := auditOpaqueAlias

run_cmd do
  let roots : List Name :=
    [``Silmaril.Wasm.Cfg.CfgSession.cfgEvFunXPS, ``Silmaril.Wasm.Cfg.CfgSession.cfgEvPendXPS,
      ``Silmaril.Wasm.Cfg.CfgSession.cfgEvInfNXP, ``Silmaril.Wasm.Cfg.CfgClosure.cfgEvFunDXPSC,
      ``Silmaril.Wasm.Cfg.CfgClosure.LDLcfgC, ``Silmaril.Wasm.Cfg.CfgClosure.cfgAns,
      ``Silmaril.Wasm.Cfg.CfgClosure.cfgFunDiv, ``Silmaril.Wasm.Cfg.CfgClosure.cfgSessionTripleC,
      ``Silmaril.Wasm.Cfg.CfgInst.cfgInstTriple, ``Silmaril.Wasm.Cfg.CfgInst.cfgInstTripleL,
      ``Silmaril.Wasm.Cfg.CfgInst.cfgInstSessionsL, ``Silmaril.Wasm.Cfg.DanglingExn.cfgInstTripleU,
      ``Silmaril.Wasm.Cfg.CfgLegal.cfgSemD]
  for r in roots do
    let v ← violations r
    unless v.isEmpty do throwError m!"audit failed: {v}"
    let ax ← badAxioms r
    unless ax.isEmpty do throwError m!"{r} depends on non-standard axioms {ax}"
  -- Positive controls.
  let (seen, _) := reach (← getEnv) [``Silmaril.Wasm.Cfg.CfgSession.cfgSessionTriple]
  unless seen.contains ``Silmaril.Wasm.Abstract.XRecursionP.closedCallXP &&
      seen.contains ``Silmaril.Wasm.Abstract.XDivergeP.FunDivXP do
    throwError "control failed: the walk no longer sees the native instance's dependency"
  if (← violations ``auditOpaqueRoot).isEmpty then
    throwError "control failed: an opaque alias of the native oracle passed the audit"
  if (← badAxioms ``sorryAx).isEmpty then
    throwError "control failed: the axiom check accepted sorryAx"

end Silmaril.Wasm.Cfg.Proofs.CfgClosureAudit
