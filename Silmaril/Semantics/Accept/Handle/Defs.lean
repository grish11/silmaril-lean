module

public import Silmaril.Semantics.Accept.Host.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.Forall2

/-!
# Handle-based acceptance APIs: writers, readers and their invalid-use policies

A module that accepts *trees* rather than bytes talks to its environment through **handles**:
opaque values (`H`, `i32` in Wasm) that the environment interprets as trees (`X`). This file is
the language-independent semantics; the S-expression and AST instances are in
`Silmaril.Formats.SExp.Api`, the Wasm link in `Silmaril.Wasm.Game.HandleAccept`.

## Writers (constructor APIs)

A writer signature `Writer Op X` has operations `Op` (a constructor with its payload: a symbol
`symbol "a"`, a list node `sexp`, a `cons`, a tagged node with arguments, …) and
`build op ts : Option X`, the tree a call of `op` denotes when its handle arguments denote `ts`
(`none`: ill-formed, e.g. a wrong arity). A trace of the module records `WEv` events:

* `write op args ret`: the module called `op` with handle arguments `args` and got `ret`;
* `accept h`: the module called `accept(h)` (recorded at the call, before any answer);
* `acceptErr h ok`: the error-return variant `accept(h) -> result`, answered `ok`;
* `acceptAll`: accept every tree constructed since the start;
* `acceptBatch keep`: accept (`keep`) or drop the trees constructed since the previous
  `acceptBatch`, and start a new batch;
* `enter`: the **export-call boundary**: the environment calls an export of the module (decoded
  from the export-call move of a game play, `Silmaril.Wasm.Game.HandleAccept.playEvents`).

The environment's state `WState` holds the **store** `σ : Env H X` (the partial meaning of every
handle allocated so far), the current batch and a `Phase` (`live`; `aborted` after a call-local
trap, until the next export call; `dead` after a session abort; `chaos` after undefined
behaviour). `WStep W pol fix` is its response relation:

* **successful writes** return a handle that is not the sentinel and is either fresh
  (`σ ret = none`) or, when the policy allows interning, already denotes the same tree
  (`Fresh`). Handles are otherwise arbitrary: nothing fixes their numeric value. A successful
  handle is never reused for another tree, so its meaning is **persistent**.
* **failures**: with a sentinel (`pol.sentinel = some s`, `0` or `-1` for `i32`), any valid write
  may return `s` (allocation failure: capacity is the host's business) and the store does not
  change. An invalid write (an argument not allocated, or `build = none`) follows `pol.onWrite`:
  `trap` (no answer), `fail` (it returns the sentinel), `ub` (undefined behaviour).
* **invalid accept** (`accept h` with `σ h = none`) follows `pol.onAccept`:
  - `callTrap`, the **Wasm-faithful mandatory trap** (the default): the current export call is
    aborted (phase `aborted`, nothing accepted); no event but `enter` may follow, and the next
    export call resumes in `live` **with the store and batch unchanged**. As in Wasm, a trap
    aborts only the current export invocation: the instance and its store persist and nothing
    performed before the trap is rolled back (successful writes stay allocated);
  - `sessionTrap`, an optional stricter policy: the whole session is aborted (phase `dead`,
    nothing may follow, not even another export call);
  - `ignore`: it returns, accepting nothing (it may still trap, like any foreign call, since a
    trace may end anywhere);
  - `ub`.
* **export calls** (`enter`) are answered in `live` and `aborted` (both moving to `live`, the
  store unchanged), not in `dead`.
* **undefined behaviour** without a fixed environment (`fix = none`) is the top element: the
  phase becomes `chaos`, the event accepts every tree, and every later event is allowed and
  accepts every tree.
* **UB restricted to a fixed environment** (`fix = some ρ`, `ρ : Env H X` a fixed `i32 → tree`
  map; total maps are `Env.ofTotal`): every successful write must agree with `ρ`
  (`ρ ret = some t`), an invalid write reads its arguments through `ρ`, and an invalid
  `accept h` accepts `ρ h` (nothing when `ρ h = none`). The union over `ρ` lies between `ignore`
  and `ub` (`Thms`), and is strictly smaller than `ub` because a *later* allocation constrains
  an earlier unallocated accept (`Examples`).

Error-return accept (`acceptErr`) is not undefined: valid handles answer `true` and accept their
tree, invalid ones answer `false`. `acceptAll` accepts the range of the store; the constructed
set is downward closed under any child relation of the signature (`Thms`), while a batch is not
(`Examples`).

## Readers (inspection APIs)

A reader signature `Reader Q A H X` has queries `Q` (`tag h`, `symbol h`, `children h`,
`child h i`, …) with answers `A`: `valid ρ q` says the query makes sense in the environment
`ρ : Env H X` and `ok ρ q a` which answers are correct (a relation: `sexp(h)` may name a child
with any handle denoting it). Events `REv`: `read q a` and `accept h`. The environment is a
**fixed** `ρ`, chosen by the quantification (`readerLang … Envs`); the module chooses which
handles to inspect and when to accept, across any sequence of export calls (`REv.enter`, the
export-call boundary). An invalid `accept` follows `OnInvalid` as for writers (`callTrap`: the
current call is aborted until the next `enter`; `sessionTrap`: the session is aborted). Invalid
queries follow `OnBadRead`:

* `arbitrary`: any answer, and the environment stays well-behaved (*not* undefined behaviour:
  later valid queries and accepts are still answered from `ρ`);
* `trap`: no answer. A query without an answer is a trap of the host call; in a game play the
  trap answer decodes to no event and the export call it belongs to ends, so the read is simply
  absent from the trace (later export calls may still follow). Every `read` event that does occur
  is answered correctly, which is what certificates use (`Thms.trap_reads_correct`);
* `dflt d`: the fixed answer `d q` (a typed error when it is disjoint from every correct answer,
  `ErrorDisjoint`; a default value otherwise);
* `ub`: undefined behaviour, the top element as for writers.

## Combined writer and reader (`CEv`, `combined`)

Reads are answered from the **current store** (in `live` only: no read follows a call-local
trap before the next export call, `.w .enter`); with a monotone reader (`Reader.Mono`) every
answer, and every successful write's meaning, stays correct for all later reads (`Thms`).

## Node environments

A fixed environment of finite trees is an `Env H X`. An environment given *node by node*
(`NodeEnv H N`: a label and child handles per handle) can contain cycles; it denotes trees only
through `Unfold`, unfolding to some finite depth (`UnfoldN`), and a handle on a cycle
unfolds to nothing (`Thms`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept.Handle

universe u v w x

/-! ## Environments -/

/-- A partial handle environment: the tree each handle denotes. -/
abbrev Env (H : Type u) (X : Type v) := H → Option X

namespace Env

variable {H : Type u} {X : Type v}

/-- The empty environment. -/
def empty : Env H X := fun _ => none

/-- A total environment `i32 → tree`. -/
def ofTotal (f : H → X) : Env H X := fun h => some (f h)

/-- `ρ'` extends `ρ`: every handle defined in `ρ` keeps its meaning. -/
def Extends (ρ ρ' : Env H X) : Prop := ∀ ⦃h x⦄, ρ h = some x → ρ' h = some x

/-- The trees denoted by some handle. -/
def range (ρ : Env H X) : Set X := {x | ∃ h, ρ h = some x}

/-- The meanings of a list of handles, if all are defined. -/
def lookupAll (ρ : Env H X) (hs : List H) : Option (List X) := hs.mapM ρ

end Env

/-! ## Writers -/

/-- **A writer signature**: `build op ts` is the tree a call of `op` denotes, given the trees
`ts` of its handle arguments, or `none` when the call is ill-formed. -/
structure Writer (Op : Type u) (X : Type v) where
  build : Op → List X → Option X

/-- Writer events, recorded by the module. -/
inductive WEv (Op : Type u) (H : Type v) where
  | write (op : Op) (args : List H) (ret : H)
  | accept (h : H)
  | acceptErr (h : H) (ok : Bool)
  | acceptAll
  | acceptBatch (keep : Bool)
  | enter

/-- Phases of an environment: `live`; `aborted` after a call-local trap (the current export
call was aborted; only the next export call may follow); `dead` after a session abort (nothing
may follow); `chaos` after undefined behaviour. -/
inductive Phase where
  | live
  | aborted
  | dead
  | chaos
  deriving DecidableEq

/-- What an invalid `accept` does. Ordered `sessionTrap ≤ callTrap ≤ ignore ≤ ub`
(`OnInvalid.rank`):

* `callTrap`: the **Wasm-faithful mandatory trap**. The current export call is aborted; the
  instance and its store persist, and the environment answers the next export call (`enter`).
  Effects performed before the trap (successful writes) are not rolled back.
* `sessionTrap`: an optional stricter policy, the whole session is aborted (nothing may follow).
* `ignore`: the call returns, accepting nothing.
* `ub`: undefined behaviour. -/
inductive OnInvalid where
  | sessionTrap
  | callTrap
  | ignore
  | ub
  deriving DecidableEq

/-- What an invalid write does. Ordered `trap ≤ fail ≤ ub` (`OnBadWrite.rank`). -/
inductive OnBadWrite where
  | trap
  | fail
  | ub
  deriving DecidableEq

def OnInvalid.rank : OnInvalid → Nat
  | .sessionTrap => 0
  | .callTrap => 1
  | .ignore => 2
  | .ub => 3

def OnBadWrite.rank : OnBadWrite → Nat
  | .trap => 0
  | .fail => 1
  | .ub => 2

/-- **A writer policy**. -/
structure Policy (H : Type u) where
  /-- The failure sentinel (`some 0` or `some (-1)` for `i32`), never a successful handle. -/
  sentinel : Option H := none
  /-- A successful write may return a handle already denoting the same tree. -/
  intern : Bool := true
  onAccept : OnInvalid := .callTrap
  onWrite : OnBadWrite := .trap

/-- The environment state of a writer session. -/
structure WState (H : Type u) (X : Type v) where
  store : Env H X
  batch : Set X
  phase : Phase

/-- The initial state: nothing allocated. -/
def WState.init {H : Type u} {X : Type v} : WState H X := ⟨Env.empty, ∅, .live⟩

variable {Op : Type u} {H : Type v} {X : Type w}

/-- The tree a write denotes in the store `σ`, if valid. -/
def Writer.built (W : Writer Op X) (σ : Env H X) (op : Op) (args : List H) : Option X :=
  (σ.lookupAll args).bind (W.build op)

/-- An admissible successful result `r` for the tree `t`. -/
def Fresh (pol : Policy H) (σ : Env H X) (r : H) (t : X) : Prop :=
  pol.sentinel ≠ some r ∧ (σ r = none ∨ (pol.intern = true ∧ σ r = some t))

/-- `r` agrees with the fixed environment, if any. -/
def Agrees (fix : Option (Env H X)) (r : H) (t : X) : Prop :=
  ∀ ρ, fix = some ρ → ρ r = some t

variable [DecidableEq H]

/-- **The writer response relation** (see the module docstring). -/
inductive WStep (W : Writer Op X) (pol : Policy H) (fix : Option (Env H X)) :
    WState H X → WEv Op H → WState H X → Set X → Prop where
  | writeOk {σ : Env H X} {B : Set X} {op : Op} {args : List H} {r : H} {t : X} :
      W.built σ op args = some t → Fresh pol σ r t → Agrees fix r t →
      WStep W pol fix ⟨σ, B, .live⟩ (.write op args r)
        ⟨Function.update σ r (some t), insert t B, .live⟩ ∅
  | writeFail {σ : Env H X} {B : Set X} {op : Op} {args : List H} {r : H} :
      pol.sentinel = some r → ((W.built σ op args).isSome ∨ pol.onWrite = .fail) →
      WStep W pol fix ⟨σ, B, .live⟩ (.write op args r) ⟨σ, B, .live⟩ ∅
  | writeChaos {σ : Env H X} {B : Set X} {op : Op} {args : List H} {r : H} :
      W.built σ op args = none → pol.onWrite = .ub → fix = none →
      WStep W pol fix ⟨σ, B, .live⟩ (.write op args r) ⟨σ, B, .chaos⟩ Set.univ
  | writeFixed {σ : Env H X} {B : Set X} {op : Op} {args : List H} {r : H} {t : X}
      {ρ : Env H X} :
      W.built σ op args = none → pol.onWrite = .ub → fix = some ρ →
      W.built ρ op args = some t → Fresh pol σ r t → ρ r = some t →
      WStep W pol fix ⟨σ, B, .live⟩ (.write op args r)
        ⟨Function.update σ r (some t), insert t B, .live⟩ ∅
  | acceptOk {σ : Env H X} {B : Set X} {h : H} {t : X} :
      σ h = some t → WStep W pol fix ⟨σ, B, .live⟩ (.accept h) ⟨σ, B, .live⟩ {t}
  | acceptCallTrap {σ : Env H X} {B : Set X} {h : H} :
      σ h = none → pol.onAccept = .callTrap →
      WStep W pol fix ⟨σ, B, .live⟩ (.accept h) ⟨σ, B, .aborted⟩ ∅
  | acceptSessionTrap {σ : Env H X} {B : Set X} {h : H} :
      σ h = none → pol.onAccept = .sessionTrap →
      WStep W pol fix ⟨σ, B, .live⟩ (.accept h) ⟨σ, B, .dead⟩ ∅
  | acceptIgnore {σ : Env H X} {B : Set X} {h : H} :
      σ h = none → pol.onAccept = .ignore →
      WStep W pol fix ⟨σ, B, .live⟩ (.accept h) ⟨σ, B, .live⟩ ∅
  | acceptChaos {σ : Env H X} {B : Set X} {h : H} :
      σ h = none → pol.onAccept = .ub → fix = none →
      WStep W pol fix ⟨σ, B, .live⟩ (.accept h) ⟨σ, B, .chaos⟩ Set.univ
  | acceptFixed {σ : Env H X} {B : Set X} {h : H} {ρ : Env H X} :
      σ h = none → pol.onAccept = .ub → fix = some ρ →
      WStep W pol fix ⟨σ, B, .live⟩ (.accept h) ⟨σ, B, .live⟩ {t | ρ h = some t}
  | acceptErrOk {σ : Env H X} {B : Set X} {h : H} {t : X} :
      σ h = some t → WStep W pol fix ⟨σ, B, .live⟩ (.acceptErr h true) ⟨σ, B, .live⟩ {t}
  | acceptErrBad {σ : Env H X} {B : Set X} {h : H} :
      σ h = none → WStep W pol fix ⟨σ, B, .live⟩ (.acceptErr h false) ⟨σ, B, .live⟩ ∅
  | acceptAll {σ : Env H X} {B : Set X} :
      WStep W pol fix ⟨σ, B, .live⟩ .acceptAll ⟨σ, B, .live⟩ σ.range
  | acceptBatch {σ : Env H X} {B : Set X} (keep : Bool) :
      WStep W pol fix ⟨σ, B, .live⟩ (.acceptBatch keep) ⟨σ, ∅, .live⟩ (if keep then B else ∅)
  | enter {σ : Env H X} {B : Set X} :
      WStep W pol fix ⟨σ, B, .live⟩ .enter ⟨σ, B, .live⟩ ∅
  | resume {σ : Env H X} {B : Set X} :
      WStep W pol fix ⟨σ, B, .aborted⟩ .enter ⟨σ, B, .live⟩ ∅
  | chaos {σ : Env H X} {B : Set X} (e : WEv Op H) :
      WStep W pol fix ⟨σ, B, .chaos⟩ e ⟨σ, B, .chaos⟩ Set.univ

/-- **The writer host**: `fix = none` is the plain store semantics; `fix = some ρ` restricts the
environment to the fixed `ρ` and resolves undefined behaviour through it. -/
def writer (W : Writer Op X) (pol : Policy H) (fix : Option (Env H X) := none) :
    Host (WEv Op H) X (WState H X) :=
  ⟨WState.init, WStep W pol fix⟩

/-- **The writer language** of a set of module traces (store semantics). -/
def writerLang (W : Writer Op X) (pol : Policy H) (T : Set (List (WEv Op H))) : Set X :=
  (writer W pol).lang T

/-- **The writer language over fixed environments**: some fixed `ρ` (from `Envs`) agreeing with
every allocation; undefined behaviour is resolved through `ρ`. -/
def fixedLang (W : Writer Op X) (pol : Policy H) (Envs : Set (Env H X))
    (T : Set (List (WEv Op H))) : Set X :=
  langOver (fun ρ : Envs => writer W pol (some ρ.1)) T

/-- The handles returned by successful writes along a trace (results other than the
sentinel). -/
def successes (pol : Policy H) : List (WEv Op H) → List H
  | [] => []
  | .write _ _ r :: es => if pol.sentinel = some r then successes pol es else r :: successes pol es
  | _ :: es => successes pol es

/-- The error-return variant read as the plain one: `acceptErr h _` becomes `accept h`. -/
def WEv.eraseErr : WEv Op H → WEv Op H
  | .acceptErr h _ => .accept h
  | e => e

/-- Map the operations of a writer event. -/
def WEv.mapOp {Op' : Type u} (f : Op → Op') : WEv Op H → WEv Op' H
  | .write op args r => .write (f op) args r
  | .accept h => .accept h
  | .acceptErr h b => .acceptErr h b
  | .acceptAll => .acceptAll
  | .acceptBatch b => .acceptBatch b
  | .enter => .enter

/-- **A writer homomorphism**: operations map along `f`, trees along the injective `g`, and
building commutes with both. -/
structure Writer.Hom {Op' : Type u} {X' : Type w} (W : Writer Op X) (W' : Writer Op' X')
    (f : Op → Op') (g : X → X') : Prop where
  inj : Function.Injective g
  build : ∀ op ts, W'.build (f op) (ts.map g) = (W.build op ts).map g

/-- Rename handles by `π` (results, arguments and accepted handles). -/
def WEv.rename (π : H → H) : WEv Op H → WEv Op H
  | .write op args r => .write op (args.map π) (π r)
  | .accept h => .accept (π h)
  | .acceptErr h b => .acceptErr (π h) b
  | .acceptAll => .acceptAll
  | .acceptBatch b => .acceptBatch b
  | .enter => .enter

/-- The policy with its sentinel renamed along `π`. -/
def Policy.rename (π : H ≃ H) (pol : Policy H) : Policy H :=
  {pol with sentinel := pol.sentinel.map π}

/-- The handles a writer event mentions as arguments (`accept` included). -/
def WEv.uses : WEv Op H → List H
  | .write _ args _ => args
  | .accept h => [h]
  | .acceptErr h _ => [h]
  | _ => []

/-! ## Readers -/

/-- **A reader signature**: `valid ρ q` and the correct answers `ok ρ q a`. -/
structure Reader (Q : Type u) (A : Type v) (H : Type w) (X : Type x) where
  valid : Env H X → Q → Prop
  ok : Env H X → Q → A → Prop

/-- Reader events. -/
inductive REv (Q : Type u) (A : Type v) (H : Type w) where
  | read (q : Q) (a : A)
  | accept (h : H)
  | enter

/-- What an invalid query answers. -/
inductive OnBadRead (Q : Type u) (A : Type v) where
  | arbitrary
  | trap
  | dflt (d : Q → A)
  | ub

/-- The answers an invalid query may get (`none`: undefined behaviour). -/
def badAnswers {Q : Type u} {A : Type v} (pol : OnBadRead Q A) (q : Q) : Option (Set A) :=
  match pol with
  | .arbitrary => some Set.univ
  | .trap => some ∅
  | .dflt d => some {d q}
  | .ub => none

/-- The answers allowed for a query (`none`: undefined behaviour). -/
noncomputable def answers {Q : Type u} {A : Type v} {H' : Type w} {X' : Type x}
    (R : Reader Q A H' X') (pol : OnBadRead Q A) (ρ : Env H' X') (q : Q) : Option (Set A) :=
  open Classical in
  if R.valid ρ q then some {a | R.ok ρ q a} else badAnswers pol q

/-- The default answers `d` are a **typed error**: never a correct answer. -/
def ErrorDisjoint {Q : Type u} {A : Type v} {H' : Type w} {X' : Type x} (R : Reader Q A H' X')
    (d : Q → A) : Prop :=
  ∀ ρ q a, R.ok ρ q a → a ≠ d q

/-- The reader is **monotone**: validity and correct answers survive store extension. -/
def Reader.Mono {Q : Type u} {A : Type v} {H' : Type w} {X' : Type x} (R : Reader Q A H' X') :
    Prop :=
  (∀ ⦃ρ ρ' q⦄, ρ.Extends ρ' → R.valid ρ q → R.valid ρ' q) ∧
  (∀ ⦃ρ ρ' q a⦄, ρ.Extends ρ' → R.valid ρ q → R.ok ρ q a → R.ok ρ' q a)

section Reader

variable {Q : Type u} {A : Type v} {H' : Type w} {X' : Type x}

/-- **The reader response relation** in the fixed environment `ρ`. -/
inductive RStep (R : Reader Q A H' X') (pol : OnBadRead Q A) (onAccept : OnInvalid)
    (ρ : Env H' X') : Phase → REv Q A H' → Phase → Set X' → Prop where
  | read {q : Q} {a : A} {S : Set A} :
      answers R pol ρ q = some S → a ∈ S → RStep R pol onAccept ρ .live (.read q a) .live ∅
  | readChaos {q : Q} {a : A} :
      answers R pol ρ q = none → RStep R pol onAccept ρ .live (.read q a) .chaos Set.univ
  | acceptOk {h : H'} {t : X'} :
      ρ h = some t → RStep R pol onAccept ρ .live (.accept h) .live {t}
  | acceptCallTrap {h : H'} :
      ρ h = none → onAccept = .callTrap → RStep R pol onAccept ρ .live (.accept h) .aborted ∅
  | acceptSessionTrap {h : H'} :
      ρ h = none → onAccept = .sessionTrap → RStep R pol onAccept ρ .live (.accept h) .dead ∅
  | acceptIgnore {h : H'} :
      ρ h = none → onAccept = .ignore → RStep R pol onAccept ρ .live (.accept h) .live ∅
  | acceptChaos {h : H'} :
      ρ h = none → onAccept = .ub → RStep R pol onAccept ρ .live (.accept h) .chaos Set.univ
  | enter : RStep R pol onAccept ρ .live .enter .live ∅
  | resume : RStep R pol onAccept ρ .aborted .enter .live ∅
  | chaos (e : REv Q A H') : RStep R pol onAccept ρ .chaos e .chaos Set.univ

/-- **The reader host** of the fixed environment `ρ`. -/
def reader (R : Reader Q A H' X') (pol : OnBadRead Q A) (onAccept : OnInvalid)
    (ρ : Env H' X') : Host (REv Q A H') X' Phase :=
  ⟨.live, RStep R pol onAccept ρ⟩

/-- **The reader language**: accepted in some environment of `Envs`. -/
def readerLang (R : Reader Q A H' X') (pol : OnBadRead Q A) (onAccept : OnInvalid)
    (Envs : Set (Env H' X')) (T : Set (List (REv Q A H'))) : Set X' :=
  langOver (fun ρ : Envs => reader R pol onAccept ρ.1) T

/-- The reads of a trace. -/
def REv.reads : List (REv Q A H') → List (Q × A)
  | [] => []
  | .read q a :: es => (q, a) :: REv.reads es
  | .accept _ :: es => REv.reads es
  | .enter :: es => REv.reads es

end Reader

/-! ## Combined writer and reader -/

/-- Events of a combined session. -/
inductive CEv (Op : Type u) (H : Type v) (Q : Type w) (A : Type x) where
  | w (e : WEv Op H)
  | r (q : Q) (a : A)

/-- **The combined response relation**: writes as `WStep` (store semantics); reads answered
from the current store. -/
inductive CStep {Q : Type u} {A : Type u} (W : Writer Op X) (R : Reader Q A H X) (pol : Policy H)
    (rpol : OnBadRead Q A) : WState H X → CEv Op H Q A → WState H X → Set X → Prop where
  | w {s s' : WState H X} {e : WEv Op H} {S : Set X} :
      WStep W pol none s e s' S → CStep W R pol rpol s (.w e) s' S
  | read {σ : Env H X} {B : Set X} {q : Q} {a : A} {S : Set A} :
      answers R rpol σ q = some S → a ∈ S →
      CStep W R pol rpol ⟨σ, B, .live⟩ (.r q a) ⟨σ, B, .live⟩ ∅
  | readChaos {σ : Env H X} {B : Set X} {q : Q} {a : A} :
      answers R rpol σ q = none →
      CStep W R pol rpol ⟨σ, B, .live⟩ (.r q a) ⟨σ, B, .chaos⟩ Set.univ
  | readInChaos {σ : Env H X} {B : Set X} {q : Q} {a : A} :
      CStep W R pol rpol ⟨σ, B, .chaos⟩ (.r q a) ⟨σ, B, .chaos⟩ Set.univ

/-- **The combined host**. -/
def combined {Q : Type u} {A : Type u} (W : Writer Op X) (R : Reader Q A H X) (pol : Policy H)
    (rpol : OnBadRead Q A) : Host (CEv Op H Q A) X (WState H X) :=
  ⟨WState.init, CStep W R pol rpol⟩

end Silmaril.Accept.Handle

namespace Silmaril.Accept.Handle

universe u v w

/-! ## Node environments -/

/-- An environment given node by node: a label and the child handles. It may have cycles. -/
abbrev NodeEnv (H : Type u) (N : Type v) := H → Option (N × List H)

/-- Unfoldings of depth at most `n`, with node builder `mk`. -/
def UnfoldN {H : Type u} {N : Type v} {X : Type w} (mk : N → List X → Option X)
    (ν : NodeEnv H N) : Nat → H → X → Prop
  | 0, _, _ => False
  | n + 1, h, x => ∃ m hs xs, ν h = some (m, hs) ∧ List.Forall₂ (UnfoldN mk ν n) hs xs ∧
      mk m xs = some x

/-- **The finite unfoldings** of a node environment: of some finite depth. -/
def Unfold {H : Type u} {N : Type v} {X : Type w} (mk : N → List X → Option X)
    (ν : NodeEnv H N) (h : H) (x : X) : Prop :=
  ∃ n, UnfoldN mk ν n h x

/-- The tree environment of a node environment: the unique finite unfolding, if any
(classical choice). -/
noncomputable def realize {H : Type u} {N : Type v} {X : Type w} (mk : N → List X → Option X)
    (ν : NodeEnv H N) : Env H X :=
  open Classical in fun h => if hx : ∃ x, Unfold mk ν h x then some hx.choose else none

/-- A tree environment **realizes** a node environment: exactly the finite unfoldings. -/
def Realizes {H : Type u} {N : Type v} {X : Type w} (mk : N → List X → Option X)
    (ν : NodeEnv H N) (ρ : Env H X) : Prop :=
  ∀ h x, ρ h = some x ↔ Unfold mk ν h x

end Silmaril.Accept.Handle

namespace Silmaril.Accept.Handle

universe u v w x

variable {Op : Type u} {H : Type v} {X : Type w}

/-! ## Orders, trace classes and certificates -/

/-- `pol` is at most as permissive as `pol'`: the same sentinel, interning only if `pol'`
interns, and invalid uses ranked `sessionTrap ≤ callTrap ≤ ignore ≤ ub` (accepts) and
`trap ≤ fail ≤ ub` (writes). -/
def Policy.Le (pol pol' : Policy H) : Prop :=
  pol.sentinel = pol'.sentinel ∧ (pol.intern = true → pol'.intern = true) ∧
    pol.onAccept.rank ≤ pol'.onAccept.rank ∧ pol.onWrite.rank ≤ pol'.onWrite.rank

/-- No write of the trace returns `s`: the sentinel is never exercised. -/
def NoRet (s : H) (t : List (WEv Op H)) : Prop :=
  ∀ op args, WEv.write op args s ∉ t

/-- **At most one allocation failure, never used afterwards**: the trace never receives the
sentinel `s`, or receives it from exactly one write and then never passes `s` to the API. -/
def OneUnusedFailure (s : H) (t : List (WEv Op H)) : Prop :=
  NoRet s t ∨ ∃ u op args v, t = u ++ WEv.write op args s :: v ∧ NoRet s u ∧ NoRet s v ∧
    ∀ e ∈ v, s ∉ e.uses

/-- The module ignores the result of `acceptErr`: changing it gives another trace. -/
def ResultOblivious (T : Set (List (WEv Op H))) : Prop :=
  ∀ t ∈ T, ∀ t', t'.map WEv.eraseErr = t.map WEv.eraseErr → t' ∈ T

/-- Only writes and `acceptAll`: the constructed-set-as-accepted variant. -/
def AllOnly : WEv Op H → Prop
  | .write _ _ _ => True
  | .acceptAll => True
  | _ => False

/-- A set is downward closed under the child relation `Sub`. -/
def DownClosed (Sub : X → X → Prop) (L : Set X) : Prop := ∀ ⦃t⦄, t ∈ L → ∀ ⦃c⦄, Sub c t → c ∈ L

/-- Every `Sub`-child of a built tree is one of the call's arguments. -/
def Writer.ChildRel (W : Writer Op X) (Sub : X → X → Prop) : Prop :=
  ∀ ⦃op ts t⦄, W.build op ts = some t → ∀ c, Sub c t → c ∈ ts

/-- Reader policies ordered by permissiveness: `trap` below everything, a default below
`arbitrary`, everything below `ub`. -/
inductive OnBadRead.Le {Q : Type u} {A : Type v} : OnBadRead Q A → OnBadRead Q A → Prop where
  | refl (p : OnBadRead Q A) : OnBadRead.Le p p
  | trap (p : OnBadRead Q A) : OnBadRead.Le .trap p
  | dflt (d : Q → A) : OnBadRead.Le (.dflt d) .arbitrary
  | ub (p : OnBadRead Q A) : OnBadRead.Le p .ub

/-- **A sound certificate** for `L`: whenever the reads `hist` are correct answers in `ρ`, the
certificate for `h` guarantees that `h` denotes a member of `L`. -/
def CertSound {Q : Type u} {A : Type v} {H' : Type w} {X' : Type x} (R : Reader Q A H' X')
    (cert : List (Q × A) → H' → Prop) (L : Set X') : Prop :=
  ∀ ρ hist h, (∀ p ∈ hist, R.valid ρ p.1 ∧ R.ok ρ p.1 p.2) → cert hist h →
    ∀ t, ρ h = some t → t ∈ L

/-- **Certified traces**: every `accept h` is preceded by reads certifying `h`. -/
def Certified {Q : Type u} {A : Type v} {H' : Type w} (cert : List (Q × A) → H' → Prop)
    (T : Set (List (REv Q A H'))) : Prop :=
  ∀ t ∈ T, ∀ u v h, t = u ++ REv.accept h :: v → cert (REv.reads u) h

/-- Reachability through child handles. -/
def NodeEnv.Child {H' : Type v} {N : Type w} (ν : NodeEnv H' N) (h' h : H') : Prop :=
  ∃ n hs, ν h = some (n, hs) ∧ h' ∈ hs

end Silmaril.Accept.Handle
