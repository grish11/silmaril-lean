module

public import Silmaril.Wasm.Cfg.CfgClosure.Defs
public import Silmaril.Wasm.Abstract.NodeBridge.Defs
public import Silmaril.Wasm.Abstract.HostStratXP.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Defs

/-!
# Instance sessions built from the self-contained CFG closure: definitions

A scalar Core 3.0 instance `I` is a session object `InstSession.instSession I P s =
threadS (instTripleS I P) s` on its import signature `I.E`. `NodeBridge` reads the instance
triple as the view of the open Core triple at the universal store-preserving host `instHost I`
(`instTripleS_eq_viewTriple`). This module builds the same kind of object from the
self-contained CFG closure `CfgClosure.cfgSessionTripleC` (every body run on the logged CFG
machine, every closed answer and callee divergence CFG-defined).

## The obstruction: host exceptions

`instHost I` answers an import call by **any** answer of the import type, including
`Answer.throw t` with an arbitrary address `t`. The native↔Core bridge
(`HostSessionXP.natTripleSXP_eq_coreTripleSXP`) accepts throwing hosts (the typed host slice
`Interp.HostSliceT`), but with typed answers (`Abstract.HostTyped`, whose `ResultTyped` for a
throw needs an existing exception), which `instHost I` does not have for a dangling `t`. This
module still uses the non-throwing special case: `instHost I` is not in the native host slice
`Interp.NativeHostSlice` as soon as `I` has an import (`CfgInst.not_nativeHostSlice_instHost`),
and the explicit domain below **excludes host exceptions**: the instance triple is
restricted to logs and streams without a thrown import answer (`noThrowT`). Exceptions raised and
caught or escaping *inside* Wasm code are kept (the checker `ehExt` covers `throw`, `throw_ref`
and `try_table`).

## Definitions

* `ImportTyped I s hh`: every host function of `s` with code `.host hh` is import `hh` of `I`
  (`hh < I.imports.length`) and its type expands to the import's type. `ImportsTyped I s`: for
  every `hh`. A well-formed instance store has it (`WellFormed.host_type`).
* `NoThrow r`: the Core result `r` is not an exception; `NoThrowCall I x`: the import answer of
  `x` is not `Answer.throw`.
* `instHostNT I`: `instHost I` restricted to non-throwing answers (values or a trap), at callouts
  `hh` with `ImportTyped I s hh` at the callout store `s`. It is store-preserving, typed, in the
  native host slice and keeps the exception checker's invariants (`CfgInst.Thms`).
* `openRestrict R t`: the finished behaviours and pending calls of `t` whose logs `R` allows, and
  the productive streams `R` allows (`hostObsInf`). Unlike `StratHost.hostRestrict`, pending calls
  are **not** restricted to calls at which `R` stalls: every reached callout stays a pending call,
  as in the open instance triple.
* `cfgInstTriple I := viewTriple I (openRestrict (coreHostRel (instHostNT I)) cfgSessionTripleC)`:
  the CFG instance triple on `I.E`. It does not depend on a profile.
* `noThrowT I t`: an instance triple restricted to logs and streams without a thrown import answer.
* `AgreeAt t t' s a`: the triples `t` and `t'` have the same finished behaviours, pending calls and
  productive streams at the store `s` and question `a`.
* `InstDom I s`: **the explicit domain** at the store `s`: `I` is well formed at `s`
  (`ScalarInstance.WellFormed`) and the store's functions pass the exception checker
  `StoreChkE (ehExt s.tags) s.funcs`. Checker acceptance is a hypothesis here, not derived.
* `cfgInstSessions o m`: the numeric instance `m` by the session of its CFG instance triple at
  its instantiation store when it has **no imports** and is in the domain there, by its Core 3.0
  instance session otherwise (compatibility only, not CFG coverage).

Theorems in `Silmaril.Wasm.Cfg.CfgInst.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgInst

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel)
open Silmaril.Wasm.Abstract.InstSession (Res ssig)
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable (I : ScalarInstance)

/-! ## Typed imports and non-throwing hosts -/

/-- **The host functions `.host hh` of `s` are import `hh` of `I`, at its type.** -/
def ImportTyped (s : Store Nat) (hh : Nat) : Prop :=
  ∀ fi ∈ s.funcs, fi.code = .host hh →
    ∃ hlt : hh < I.imports.length, Validation.Expand fi.type (I.imports.get ⟨hh, hlt⟩).toComp

/-- Every host function of `s` is an import of `I`, at its type. -/
def ImportsTyped (s : Store Nat) : Prop := ∀ hh, ImportTyped I s hh

/-- A Core result that is not an exception. -/
def NoThrow (r : Result) : Prop := ∀ t, r ≠ .throw t

/-- An import call whose answer is not a thrown exception. -/
def NoThrowCall (x : Call I.E) : Prop := ∀ t, x.2 ≠ .throw t

/-- **The non-throwing universal host of `I`**: `instHost I` at callouts whose host functions
are typed imports, answering values or a trap (never an exception), the store unchanged. -/
def instHostNT : HostSemantics Nat := fun hh s us out =>
  Abstract.NodeBridge.instHost I hh s us out ∧ ImportTyped I s hh ∧
    ∀ s' r, out = .returned s' r → NoThrow r

/-! ## Triples -/

/-- **The open restriction of a triple by a host**: allowed logs (finished and pending) and
allowed productive streams; every pending call after an allowed log is kept. -/
def openRestrict {E : Sig.{0}} {S A B : Type} (R : HostRel E) (t : ObsTriple E S A B) :
    ObsTriple E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ R.Consistent x.1},
    fun s a => {x | x ∈ t.2.1 s a ∧ R.Consistent x.1},
    hostObsInf R t.2.2)

/-- **The CFG instance triple**: the view, on the import signature of `I`, of the self-contained
CFG session triple openly restricted to the non-throwing universal host of `I`. -/
noncomputable def cfgInstTriple : ObsTriple I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit) :=
  Abstract.NodeBridge.viewTriple I (openRestrict (coreHostRel (instHostNT I)) CfgClosure.cfgSessionTripleC)

/-- **An instance triple without thrown import answers**: logs and streams whose import answers
are values or traps. -/
def noThrowT {S A B : Type} (t : ObsTriple I.E S A B) : ObsTriple I.E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ ∀ y ∈ x.1, NoThrowCall I y},
    fun s a => {x | x ∈ t.2.1 s a ∧ ∀ y ∈ x.1, NoThrowCall I y},
    fun s a => {ω | ω ∈ t.2.2 s a ∧ ∀ k, NoThrowCall I (ω k)})

/-- **Two triples agree at `(s, a)`**: same finished behaviours, pending calls and productive
streams. -/
def AgreeAt {E : Sig.{0}} {S A B : Type} (t t' : ObsTriple E S A B) (s : S) (a : A) : Prop :=
  t.1 s a = t'.1 s a ∧ t.2.1 s a = t'.2.1 s a ∧ t.2.2 s a = t'.2.2 s a

/-! ## The domain -/

/-- **The explicit domain at `s`**: the instance is well formed at `s`, and the store's
functions pass the exception checker. -/
structure InstDom (s : Store Nat) : Prop where
  wf : I.WellFormed s
  chk : StoreChkE (ehExt s.tags) s.funcs

open Classical in
/-- **Each numeric instance by its CFG instance session where it applies**: without imports and
in the domain at its instantiation store, the session of `cfgInstTriple`; otherwise its Core 3.0
instance session (compatibility only, not CFG coverage). -/
noncomputable def cfgInstSessions (o : GrowOracle) (m : Component.Reference.NumInstance) :
    DStrategy m.inst.E (ssig m.inst.exports) :=
  if m.inst.imports = [] ∧ InstDom m.inst m.inst.store then
    StratSession.threadS (cfgInstTriple m.inst) m.inst.store
  else Abstract.InstSession.instSession m.inst (profile o) m.inst.store

end Silmaril.Wasm.Cfg.CfgInst
