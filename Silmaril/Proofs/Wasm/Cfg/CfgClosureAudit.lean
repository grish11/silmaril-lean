module

public import Silmaril.Wasm.Cfg.CfgClosure.Defs
public import Silmaril.Wasm.Cfg.CfgInst.Defs
meta import Lean.Elab.Command

/-!
# Definition dependency audit of the CFG closure (H3, a build-time check)

Not a proof: an elaboration-time check that fails the build. From each definition of the
self-contained CFG closure (finished `cfgEvFunXPS`, pending `cfgEvPendXPS`, productive
`cfgEvInfNXP`, divergent `cfgEvFunDXPSC`, `LDLcfgC`, `cfgAns`, `cfgFunDiv`, the triple
`cfgSessionTripleC`, and the instance triples `CfgInst.cfgInstTriple`, `CfgInst.cfgInstTripleL`
and the session family `CfgInst.cfgInstSessionsL` built from it) it walks every
constant used by the types and bodies of definitions, inductive types, constructors and
recursors, transitively (theorem proofs are not followed: a proof does not change what a
definition denotes). It checks:

* no **native closed or divergent object** is reached: nothing in `XRecursionP`, `XDivergeP`,
  `XRecursion`, `XDiverge`, `Recursion`, and none of `CallXP.EvalOXP`, `wasmHOpenXPS`,
  `wasmHOpenXP`, `wasmEvFunXPS`, `wasmEvFunXP`, `wasmEvFunDXP`, `wasmEvFunDXPS`,
  `wasmEvPendXPS`, `wasmEvInfNXP`, `sessionTripleXP`, `LogDivXP`, `InfLXP`, `LDLwXP`, `InfLwXP`;
* the walk is complete: no reached `Silmaril` constant is an axiom, an opaque constant or
  missing from the environment, except proofs: auxiliary proofs (`_proof_i`) and constants whose
  type is a proposition (an imported theorem appears as an axiom in a module, its proof not
  exported; `scripts/check-layout.sh` forbids `axiom` declarations in `Silmaril`);
* the check is effective: from the scoped native instance `CfgSession.cfgSessionTriple` the same
  walk reaches `XRecursionP.closedCallXP` and `XDivergeP.FunDivXP`.

What is reached from the Wasm side is the open logged relations `Abstract.EvalLXPS`/`ReachLXPS`
(every call an open entry, answered by nothing) and flow helpers.
-/

namespace Silmaril.Wasm.Cfg.Proofs.CfgClosureAudit

open Lean Elab Command

/-- The constants reachable from `roots` through definitions, and those whose body is not
available (axioms, opaque constants, missing names). -/
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

run_cmd do
  let env ← getEnv
  let roots : List Name :=
    [``Silmaril.Wasm.Cfg.CfgSession.cfgEvFunXPS, ``Silmaril.Wasm.Cfg.CfgSession.cfgEvPendXPS,
      ``Silmaril.Wasm.Cfg.CfgSession.cfgEvInfNXP, ``Silmaril.Wasm.Cfg.CfgClosure.cfgEvFunDXPSC,
      ``Silmaril.Wasm.Cfg.CfgClosure.LDLcfgC, ``Silmaril.Wasm.Cfg.CfgClosure.cfgAns,
      ``Silmaril.Wasm.Cfg.CfgClosure.cfgFunDiv, ``Silmaril.Wasm.Cfg.CfgClosure.cfgSessionTripleC,
      ``Silmaril.Wasm.Cfg.CfgInst.cfgInstTriple, ``Silmaril.Wasm.Cfg.CfgInst.cfgInstTripleL,
      ``Silmaril.Wasm.Cfg.CfgInst.cfgInstSessionsL]
  for r in roots do
    let (seen, unseen) := reach env [r]
    let bad := seen.toList.filter isNative
    unless bad.isEmpty do
      throwError m!"{r} reaches native closed or divergent objects: {bad}"
    let hid := unseen.toList.filter fun n => (`Silmaril).isPrefixOf n && !isProofAux n
    let hid ← hid.filterM fun n => do
      let some ci := env.find? n | return true
      return !(← liftTermElabM (Meta.isProp ci.type))
    unless hid.isEmpty do
      throwError m!"{r}: the walk does not see the bodies of {hid}"
  let (seen, _) := reach env [``Silmaril.Wasm.Cfg.CfgSession.cfgSessionTriple]
  unless seen.contains ``Silmaril.Wasm.Abstract.XRecursionP.closedCallXP &&
      seen.contains ``Silmaril.Wasm.Abstract.XDivergeP.FunDivXP do
    throwError "the audit no longer sees the native instance's dependency: check the walk"

end Silmaril.Wasm.Cfg.Proofs.CfgClosureAudit
