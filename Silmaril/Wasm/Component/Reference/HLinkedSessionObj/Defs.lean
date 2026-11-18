module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionInf.Defs
public import Silmaril.Games.Abstract.StratLegal.Defs
public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Session objects of linked components with host imports: definitions

**Scope.** `HLinked2` (`HLinkedSession.Defs`): the import-free exporter A (`l.exp`) answers the
wired imports of the importer B (`l.imp`), and B's remaining imports are host imports of the
parent, passed through. The host calls are visible lower moves of the session object, on the
host interface `sigN l.host.length`. The definitions come from the specification
(`HLinked2.SessSpec`, `Linked2.DivRound`, `ImpRel`, `ExpRunH`), not from `Comp.den`.

## Which host answers the reference observes

The reference equivalence `HLinked2.RefSessEquivFull` (`HLinkedSessionInf.Defs`) observes a
linked component under the logging host `answerHostS P (logG g)` of a **typed deterministic
stateful** answering function `g : σ → HostFuncId → List RVal → Option (List RVal × σ)`
(`HLinked2.HostTyped`). The inputs of `g` are its state, the host function and the reference
images of the arguments, nothing else (no store view). Three consequences:

* **Ill-typed answers are never given.** `HLinked2.hostLegal h` admits a refusal `none` and the
  answers `some (.vals us)` of the import's result types. The session object lives on the legal
  interface `HLinked2.hostSig h := StratLegal.legalSig (sigN h.length) (hostLegal h)`, so an
  ill-typed answer is not an Opponent move at all.
* **A refusal keeps the host state** (`HostAnswersS`: a refused call leaves `s' = s`). Hence a
  call refused since the last answered call is refused again (`HLinked2.Forced`, first case),
  and a call of an import whose result types have no values (`HLinked2.Answerable`) is always
  refused (second case). Such a **forced refusal** says nothing about the call: the reference
  log records answered calls only, and every typed host refuses it.
* **Every other history is realised**: a fresh monotone counter host answers the `n`-th answered
  call of a script and refuses everything else (`HLinked2.scriptG`); it never revisits a host
  state.

`HLinked2.VisRun h R c R'` is a history `c` of visible host calls with legal answers, `R` the
calls refused since the last answered call: no visible call is a forced refusal, a refusal adds
its call to `R`, an answer resets `R`. `HLinked2.RealRun h R c R'` also allows forced refusals
(leaving `R`): the histories a deterministic typed host can produce (the realizability theorems
in `Thms`).

## The triple and the session object

The state is `(u, π, R)`: the importer's store, the exporter's store and the calls refused since
the last answered call. `HLinked2.compFin P l Ie Ii`:

* an untyped question (`Linked2.typedQ` fails) traps at once, the state unchanged;
* a typed call `(j, vs)` is a one-round `SessSpec` whose host calls `c` are a `VisRun` from `R`
  to `R'`, ending at `(u', π', R')` with the outcome (a value, or a continuing trap);
* or a one-round `SessSpec` with host calls `c ++ [⟨m, none⟩]` and a trap, `c` a `VisRun` from
  `R` to `R'` and `m` forced at `R'`: the **forced refusal is hidden**, the round is a continuing
  trap with the log `c`, ending at `(u', π', R')`;
* or the round diverges after the host calls `c` (`HLinked2.RoundDivC`, the host-free form of
  `HLinked2.RoundDiv`), `c` a `VisRun` from `R`.

The productive streams are the host chatter (`HLinked2.RoundInfC`: B makes infinitely many
import calls, among them infinitely many host calls, forming the stream `ω`), every prefix of `ω`
a `VisRun`. `HLinked2.compTripleR` is the saturation (`StratObs.sat`) of this triple on
`sigN l.host.length`; `HLinked2.compTripleS` is its restriction to the legal interface
(`StratLegal.restrict`), and
`HLinked2.compSession P l := threadS (compTripleS P l Ie Ii) (Ii.store, Ie.store, [])` for the
instances of the two core modules.

**The open object.** `HLinked2.compTripleO` and `HLinked2.compSessionO` are the same without
`VisRun` and without hiding forced refusals: every legal answer is an Opponent move. Their
equality is a stronger, open-interface equivalence: it distinguishes plays that no deterministic
host realises (a call refused and then answered with no answered call in between).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace HLinked2

/-! ## The legal host interface -/

/-- **The legal answers to a host call**: a refusal, or IR values of the result types of the
host import. -/
def hostLegal (h : Iface) (m : (sigN h.length).Op) : Option Payload → Prop
  | none => True
  | some (.vals us) => ValTy.checkList h[m.1].2.results us = true
  | some (.flat _) => False

/-- **The legal host interface**: host calls answered only by refusals and typed results. -/
abbrev hostSig (h : Iface) : Sig.{0} := StratLegal.legalSig (sigN h.length) (hostLegal h)

/-- The host import of the call has some typed result. -/
def Answerable (h : Iface) (m : (sigN h.length).Op) : Prop :=
  ∃ us : List IVal, ValTy.checkList h[m.1].2.results us = true

/-- **A forced refusal**: the call was refused since the last answered call (`m ∈ R`), or its
host import has no typed result. Every typed deterministic host refuses it. -/
def Forced (h : Iface) (R : List (sigN h.length).Op) (m : (sigN h.length).Op) : Prop :=
  m ∈ R ∨ ¬ Answerable h m

/-- **A history of visible host calls**, from the refusals `R` since the last answered call to
`R'`: no call is a forced refusal, a refusal adds its call, a legal answer resets. -/
inductive VisRun (h : Iface) :
    List (sigN h.length).Op → List (Call (sigN h.length)) → List (sigN h.length).Op → Prop
  | nil (R : List (sigN h.length).Op) : VisRun h R [] R
  | refuse {R R' : List (sigN h.length).Op} {m : (sigN h.length).Op}
      {c : List (Call (sigN h.length))} :
      ¬ Forced h R m → VisRun h (m :: R) c R' → VisRun h R (⟨m, none⟩ :: c) R'
  | answer {R R' : List (sigN h.length).Op} {m : (sigN h.length).Op} {p : Payload}
      {c : List (Call (sigN h.length))} :
      m ∉ R → hostLegal h m (some p) → VisRun h [] c R' → VisRun h R (⟨m, some p⟩ :: c) R'

/-- **A history a deterministic typed host can produce**: `VisRun`, with forced refusals
allowed (they leave `R`). -/
inductive RealRun (h : Iface) :
    List (sigN h.length).Op → List (Call (sigN h.length)) → List (sigN h.length).Op → Prop
  | nil (R : List (sigN h.length).Op) : RealRun h R [] R
  | forced {R R' : List (sigN h.length).Op} {m : (sigN h.length).Op}
      {c : List (Call (sigN h.length))} :
      Forced h R m → RealRun h R c R' → RealRun h R (⟨m, none⟩ :: c) R'
  | refuse {R R' : List (sigN h.length).Op} {m : (sigN h.length).Op}
      {c : List (Call (sigN h.length))} :
      ¬ Forced h R m → RealRun h (m :: R) c R' → RealRun h R (⟨m, none⟩ :: c) R'
  | answer {R R' : List (sigN h.length).Op} {m : (sigN h.length).Op} {p : Payload}
      {c : List (Call (sigN h.length))} :
      m ∉ R → hostLegal h m (some p) → RealRun h [] c R' → RealRun h R (⟨m, some p⟩ :: c) R'

/-- Every host call is on IR values (the form `HostAnswersS` answers). -/
def ValsCalls {n : Nat} (c : List (Call (sigN n))) : Prop :=
  ∀ x ∈ c, ∃ (k : Fin n) (ws : List IVal), x.1 = (k, .vals ws)

/-! ## The scripted host -/

/-- The answered calls of a history, in order: host import, IR arguments, IR results. -/
def answered {n : Nat} : List (Call (sigN n)) → List (Fin n × List IVal × List IVal)
  | [] => []
  | ⟨(k, .vals ws), some (.vals us)⟩ :: c => (k, ws, us) :: answered c
  | _ :: c => answered c

/-- **The scripted host** of the answered calls `S`: in state `n` it answers the `n`-th
answered call of `S`, on exactly its host function and arguments, moving to `n + 1`, and
refuses everything else. Its states only grow. -/
def scriptG {n : Nat} (S : List (Fin n × List IVal × List IVal)) :
    ℕ → Runtime.HostFuncId → List Value.Val → Option (List Value.Val × ℕ) :=
  fun i fn args => match S[i]? with
    | some (k, ws, us) =>
      if fn = ⟨k.val⟩ ∧ args = ws.map toRefVal then some (us.map toRefVal, i + 1) else none
    | none => none

/-! ## Host-free rounds -/

section Spec

/-- **A round that never answers, after the host calls `c`**: `HLinked2.RoundDiv` without a host,
the host calls of its `ExpRunH` prefix being `c` (with the answers Opponent gave). -/
def RoundDivC (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) (u π : Store Nat)
    (j : Fin l.imp.exports.length) (vs : List IVal)
    (c : List (Call (sigN l.host.length))) : Prop :=
  ∃ (d : Linked2.DivRound l.toL2 Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : Store Nat),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRunH P l Ie π d.dss.flatten π₁ ∧ l.hostCalls d.dss.flatten = c ∧
    (Linked2.DivB P s t ∨ Linked2.DivA P l.toL2 Ie Ii d.f s t π₁ ∨
      Linked2.Chatter P l.toL2 Ie Ii d.f s t π₁)

/-- **A round making infinitely many host calls `ω`**: `HLinked2.RoundInf` without a host. The
call of export `j` on `vs` asks B's instance from `u`, which then makes infinitely many core
import calls `c k`, related to component import calls `ds k` (`ImpRel`), the wired ones answered
by A from `π` on (`ExpRunH`); the host calls of the first `k` of them are the first `N k` calls
of `ω`, and `N` is unbounded. -/
def RoundInfC (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) (u π : Store Nat)
    (j : Fin l.imp.exports.length) (vs : List IVal) (ω : ℕ → Call (sigN l.host.length)) :
    Prop :=
  ∃ (f : Ii.F.Op) (xs : List Flat) (q : ℕ → Ii.HState) (c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e)
    (ds : ℕ → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))
    (πs : ℕ → Store Nat) (N : ℕ → ℕ),
    checkLower l.imp.exports[j].ty.params vs = some xs ∧ f.1.val = l.imp.exports[j].core ∧
    f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat ∧
    Ii.Path P (.idle u) [.inr (.ask f)] (q 0) ∧ πs 0 = π ∧ N 0 = 0 ∧
    (∀ k, Ii.Path P (q k) (callMoves [c k]) (q (k + 1)) ∧ ImpRel l.imp Ii (c k) (ds k) ∧
      ExpRunH P l Ie (πs k) (ds k) (πs (k + 1)) ∧
      streamTake ω (N (k + 1)) = streamTake ω (N k) ++ l.hostCalls (ds k)) ∧
    ∀ n, ∃ k, n ≤ N k

end Spec

/-! ## The host-realizable triple -/

/-- The state of the triple: the importer's store, the exporter's store, and the calls refused
since the last answered call. -/
abbrev St (l : HLinked2) : Type := Store Nat × Store Nat × List (sigN l.host.length).Op

/-- **The finished behaviours of one session call**, with the host calls visible: an untyped
question traps at once; a typed call is a one-round `SessSpec` whose host calls are a `VisRun`,
or one whose last host call is a forced refusal, hidden, followed by a trap; or a divergence
after a `VisRun`. -/
def compFin (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) :
    AFun (sigN l.host.length) l.St (Nat × Payload) (Payload ⊕ PUnit.{1}) := fun s q =>
  match l.toL2.typedQ q with
  | none => {([], .ret (.inr PUnit.unit) s)}
  | some (j, vs) =>
    {x | (∃ (o : Option (List IVal)) (u' π' : Store Nat) (R' : List (sigN l.host.length).Op),
          SessSpec P l Ie Ii s.1 s.2.1 [(j, vs)] [o] [x.1] u' π' ∧
          VisRun l.host s.2.2 x.1 R' ∧ x.2 = .ret (outAns o) (u', π', R')) ∨
      (∃ (m : (sigN l.host.length).Op) (u' π' : Store Nat) (R' : List (sigN l.host.length).Op),
          SessSpec P l Ie Ii s.1 s.2.1 [(j, vs)] [none] [x.1 ++ [⟨m, none⟩]] u' π' ∧
          VisRun l.host s.2.2 x.1 R' ∧ Forced l.host R' m ∧
          x.2 = .ret (.inr PUnit.unit) (u', π', R')) ∨
      (∃ R' : List (sigN l.host.length).Op, RoundDivC P l Ie Ii s.1 s.2.1 j vs x.1 ∧
          VisRun l.host s.2.2 x.1 R' ∧ x.2 = .div)}

/-- **The productive streams of one session call**: host chatter whose every prefix is a
`VisRun`. -/
def compInf (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) :
    PInf (sigN l.host.length) l.St (Nat × Payload) := fun s q =>
  match l.toL2.typedQ q with
  | none => ∅
  | some (j, vs) =>
    {ω | RoundInfC P l Ie Ii s.1 s.2.1 j vs ω ∧
      ∀ n, ∃ R' : List (sigN l.host.length).Op, VisRun l.host s.2.2 (streamTake ω n) R'}

/-- **The host-realizable triple** on the host interface: the saturation of `compFin` and
`compInf` (pending calls are the call prefixes they force). -/
def compTripleR (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) :
    ObsTriple (sigN l.host.length) l.St (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  sat (compFin P l Ie Ii, fun _ _ => ∅, compInf P l Ie Ii)

/-- **The store-retaining session triple** on the legal host interface. -/
def compTripleS (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) :
    ObsTriple (hostSig l.host) l.St (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  StratLegal.restrict (hostLegal l.host) (compTripleR P l Ie Ii)

/-- The session trapping every question, on any interface (for modules without an
instance). -/
def trapTriple (E : Sig.{0}) : ObsTriple E PUnit.{1} (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  (fun s _ => {([], .ret (.inr PUnit.unit) s)}, fun _ _ => ∅, fun _ _ => ∅)

open Classical in
/-- **The canonical session object of a linked component with host imports**, on the legal host
interface: the session threading of `compTripleS` from the stores of the instances of the two
core modules and no refusals. A component without instances traps on every question. -/
noncomputable def compSession (P : Profile) (l : HLinked2) :
    DStrategy (hostSig l.host) sessSig :=
  if h : ∃ Ie Ii : ScalarInstance, l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii then
    StratSession.threadS (compTripleS P l h.choose h.choose_spec.choose)
      (h.choose_spec.choose.store, h.choose.store, [])
  else StratSession.threadS (trapTriple _) PUnit.unit

/-! ## The open object -/

/-- **The finished behaviours of one session call, every legal answer allowed**: as `compFin`
without `VisRun` and without hiding forced refusals. -/
def compFinO (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) :
    AFun (sigN l.host.length) (Store Nat × Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  fun s q =>
  match l.toL2.typedQ q with
  | none => {([], .ret (.inr PUnit.unit) s)}
  | some (j, vs) =>
    {x | (∃ (o : Option (List IVal)) (u' π' : Store Nat),
          SessSpec P l Ie Ii s.1 s.2 [(j, vs)] [o] [x.1] u' π' ∧
          x.2 = .ret (outAns o) (u', π')) ∨
      (RoundDivC P l Ie Ii s.1 s.2 j vs x.1 ∧ x.2 = .div)}

/-- **The open triple** on the legal host interface: every legal answer is an Opponent move. -/
def compTripleO (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) :
    ObsTriple (hostSig l.host) (Store Nat × Store Nat) (Nat × Payload) (Payload ⊕ PUnit.{1}) :=
  StratLegal.restrict (hostLegal l.host)
    (sat (compFinO P l Ie Ii, fun _ _ => ∅, fun s q =>
      match l.toL2.typedQ q with
      | none => ∅
      | some (j, vs) => {ω | RoundInfC P l Ie Ii s.1 s.2 j vs ω}))

open Classical in
/-- **The open session object**: the threading of `compTripleO`. Its equality is an
open-interface equivalence, stronger than the reference equivalence under deterministic
hosts. -/
noncomputable def compSessionO (P : Profile) (l : HLinked2) :
    DStrategy (hostSig l.host) sessSig :=
  if h : ∃ Ie Ii : ScalarInstance, l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii then
    StratSession.threadS (compTripleO P l h.choose h.choose_spec.choose)
      (h.choose_spec.choose.store, h.choose.store)
  else StratSession.threadS (trapTriple _) PUnit.unit

/-! ## Comparing two linked components -/

/-- **The same types**: the same number of exports, of the same types, and the same host
imports. -/
structure SameTypes (l l' : HLinked2) : Prop where
  len : l.imp.exports.length = l'.imp.exports.length
  ty : ∀ j : Fin l.imp.exports.length, l'.imp.exports[Fin.cast len j].ty = l.imp.exports[j].ty
  host : l'.host = l.host

end HLinked2

end Silmaril.Wasm.Component.Reference
