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

## Host exceptions: legal and dangling

`instHost I` answers an import call by **any** answer of the import type, including
`Answer.throw a` with an arbitrary address `a`. The native↔Core bridge
(`HostSessionXP.natTripleSXP_eq_coreTripleSXP`) accepts throwing hosts (the typed host slice
`Interp.HostSliceT`) with typed answers (`Abstract.HostTyped`, whose `ResultTyped` for a throw
needs an existing exception). So the CFG reading here covers **legal** host exceptions: an import
answer `Answer.throw a` at a call whose store is `s` has `a < s.exns.length`
(`Answer.ThrowsBelow s.exns.length`, the legality of `IsInstance.adequacy`). Exceptions at
dangling addresses are not covered (see `CfgInst.Thms`, "What is not claimed"). Exceptions
raised and caught or escaping inside Wasm code are kept (the checker `ehExt` covers `throw`,
`throw_ref` and `try_table`).

## Definitions

* `ImportTyped I s hh`: every host function of `s` with code `.host hh` is import `hh` of `I`
  (`hh < I.imports.length`) and its type expands to the import's type. `ImportsTyped I s`: for
  every `hh`. A well-formed instance store has it (`WellFormed.host_type`).
* `NoThrow r`: the Core result `r` is not an exception; `NoThrowCall I x`: the import answer of
  `x` is not `Answer.throw`. `LegalRes s r`: an exception result `r` names an exception of `s`.
* `instHostQ I Q`: `instHost I` at callouts `hh` with `ImportTyped I s hh` at the callout store
  `s`, with the answers `r` such that `Q s r`. Its instances: `instHostL I` (`Q = LegalRes`, the
  **legal host**: store-preserving, typed, in `HostSliceT`, keeps the checker's invariants),
  `instHostNT I` (no exception; also in the native host slice) and `instHostU I` (every answer;
  not typed).
* `openRestrict R t`: the finished behaviours and pending calls of `t` whose logs `R` allows, and
  the productive streams `R` allows (`hostObsInf`). Unlike `StratHost.hostRestrict`, pending calls
  are **not** restricted to calls at which `R` stalls: every reached callout stays a pending call,
  as in the open instance triple.
* `cfgInstTripleL I := viewTriple I (openRestrict (coreHostRel (instHostL I)) cfgSessionTripleC)`:
  the CFG instance triple on `I.E` with legal host exceptions; `cfgInstTriple I` is the same at
  `instHostNT I`. Neither depends on a profile.
* `legalT t`: a Core triple restricted to logs and streams whose host events answer results legal
  at their call store (the store is recorded in each Core event `((hh, s, us), (s', r))`).
  `instTripleL I P := viewTriple I (legalT (coreTripleSO P (instHost I)))`: the instance triple
  `instTripleS I P` (the same view, unrestricted) restricted to legal host exceptions.
* `noThrowT I t`: an instance triple restricted to logs and streams without a thrown import answer.
* `AgreeAt t t' s a`: the triples `t` and `t'` have the same finished behaviours, pending calls and
  productive streams at the store `s` and question `a`.
* `InstDom I s`: **the explicit domain** at the store `s`: `I` is well formed at `s`
  (`ScalarInstance.WellFormed`) and the store's functions pass the exception checker
  `StoreChkE (ehExt s.tags) s.funcs`. Checker acceptance is a hypothesis here, not derived.
* `legalSemD P`: the Core 3.0 component semantics with each numeric instance interpreted by its
  legal session `threadS (instTripleL m.inst P) m.inst.store`.
* `cfgInstSessionsL m`: every numeric instance by the session of `cfgInstTripleL m.inst` at its
  instantiation store. There is **no fallback** to Core sessions; equalities with Core are stated
  on the domain only.

Theorems in `Silmaril.Wasm.Cfg.CfgInst.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgInst

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel)
open Silmaril.Wasm.Abstract.NodeBridge (instHost)
open Silmaril.Wasm.Abstract.InstSession (Res ssig)
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable (I : ScalarInstance)

/-! ## Typed imports and restricted universal hosts -/

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

/-- A Core result **legal at the store `s`**: an exception names an existing exception instance
of `s` (`a < s.exns.length`). On import answers this is `Answer.ThrowsBelow s.exns.length`
(`CfgInst.legalRes_toResult_iff`), the legality of `IsInstance.adequacy`'s environments. -/
def LegalRes (s : Store Nat) (r : Result) : Prop := ∀ a, r = .throw a → a < s.exns.length

/-- **The universal host of `I` restricted by `Q`**: `instHost I` at callouts whose host
functions are typed imports, with the answers `r` that `Q` allows at the callout store, the store
unchanged. -/
def instHostQ (Q : Store Nat → Result → Prop) : HostSemantics Nat := fun hh s us out =>
  Abstract.NodeBridge.instHost I hh s us out ∧ ImportTyped I s hh ∧
    ∀ s' r, out = .returned s' r → Q s r

/-- **The non-throwing universal host of `I`**: `instHost I` at callouts whose host functions
are typed imports, answering values or a trap (never an exception), the store unchanged. -/
def instHostNT : HostSemantics Nat := instHostQ I fun _ r => NoThrow r

/-- **The legal universal host of `I`**: `instHost I` at callouts whose host functions are typed
imports, answering values, a trap, or an exception **of the callout store**
(`LegalRes`), the store unchanged. -/
def instHostL : HostSemantics Nat := instHostQ I LegalRes

/-- **The unrestricted typed universal host of `I`**: `instHost I` at callouts whose host
functions are typed imports, with every answer, including exceptions at dangling addresses. It
is not typed (`CfgInst.not_hostTyped_instHostU`): the CFG reading does not cover it. -/
def instHostU : HostSemantics Nat := instHostQ I fun _ _ => True

/-! ## Triples -/

/-- **The open restriction of a triple by a host**: allowed logs (finished and pending) and
allowed productive streams; every pending call after an allowed log is kept. -/
def openRestrict {E : Sig.{0}} {S A B : Type} (R : HostRel E) (t : ObsTriple E S A B) :
    ObsTriple E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ R.Consistent x.1},
    fun s a => {x | x ∈ t.2.1 s a ∧ R.Consistent x.1},
    hostObsInf R t.2.2)

/-- **The throw-free CFG instance triple**: the view, on the import signature of `I`, of the
self-contained CFG session triple openly restricted to the non-throwing universal host of `I`. -/
noncomputable def cfgInstTriple : ObsTriple I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit) :=
  Abstract.NodeBridge.viewTriple I
    (openRestrict (coreHostRel (instHostNT I)) CfgClosure.cfgSessionTripleC)

/-- **An instance triple without thrown import answers**: logs and streams whose import answers
are values or traps. -/
def noThrowT {S A B : Type} (t : ObsTriple I.E S A B) : ObsTriple I.E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ ∀ y ∈ x.1, NoThrowCall I y},
    fun s a => {x | x ∈ t.2.1 s a ∧ ∀ y ∈ x.1, NoThrowCall I y},
    fun s a => {ω | ω ∈ t.2.2 s a ∧ ∀ k, NoThrowCall I (ω k)})

/-- **A Core triple restricted to legal host events**: logs and streams in which every host event
`ev = ((hh, s, us), (s', r))` answers a result legal at its call store (`LegalRes s r`). -/
def legalT {S A B : Type} (t : ObsTriple (wasmHostSig Nat) S A B) :
    ObsTriple (wasmHostSig Nat) S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ ∀ ev ∈ x.1, LegalRes ev.1.2.1 ev.2.2},
    fun s a => {x | x ∈ t.2.1 s a ∧ ∀ ev ∈ x.1, LegalRes ev.1.2.1 ev.2.2},
    fun s a => {ω | ω ∈ t.2.2 s a ∧ ∀ k, LegalRes (ω k).1.2.1 (ω k).2.2})

/-- **The instance triple with legal host exceptions**: the view on `I.E` of the open Core triple
of the universal host `instHost I`, restricted to legal host events (`legalT`). The instance
triple `instTripleS I P` is the same view without the restriction
(`NodeBridge.instTripleS_eq_viewTriple`), so this is `instTripleS I P` restricted to the logs and
streams having a Core witness whose thrown import answers name exceptions of the store **at that
call**. (An import call `Call I.E` does not record its store, so the restriction is stated on
the Core events, which do.) -/
noncomputable def instTripleL (P : Numerics.Profile) :
    ObsTriple I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit) :=
  Abstract.NodeBridge.viewTriple I (legalT (Abstract.NodeBridge.coreTripleSO P (instHost I)))

/-- **The CFG instance triple with legal host exceptions**: the view, on the import signature of
`I`, of the self-contained CFG session triple openly restricted to the legal universal host of
`I`. -/
noncomputable def cfgInstTripleL : ObsTriple I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit) :=
  Abstract.NodeBridge.viewTriple I
    (openRestrict (coreHostRel (instHostL I)) CfgClosure.cfgSessionTripleC)

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

/-! ## Session families -/

/-- **The legal Core 3.0 semantics**: each numeric instance by the session of its instance triple
with legal host exceptions (`instTripleL`), at its instantiation store. -/
noncomputable def legalSemD (P : Numerics.Profile) :
    Component.DCoreSem Component.Reference.NumInstance :=
  Abstract.InstSession.threadSemSD fun m =>
    StratSession.threadS (instTripleL m.inst P) m.inst.store

/-- **Each numeric instance by its CFG instance session**, with no fallback: the session of
`cfgInstTripleL` at its instantiation store. -/
noncomputable def cfgInstSessionsL (m : Component.Reference.NumInstance) :
    DStrategy m.inst.E (ssig m.inst.exports) :=
  StratSession.threadS (cfgInstTripleL m.inst) m.inst.store

end Silmaril.Wasm.Cfg.CfgInst
