module

public import Silmaril.Wasi.Component.Consequence.Signed.Defs
public import Silmaril.Logic.Consequence.Interp.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-! # Protocol readings as interpretations

The protocol readings as core interpretations (`Silmaril.Consequence.Interp`): a value read under
a typed configuration as a consequence system, or `none` when it cannot be read.

* **Trace values** (`Set (List WEv)`): `batchInterp`, `seqInterp`, `assumeAssertInterp` (and its
  sequent form `assumeAssertSeqInterp`) are always defined. The configuration types
  (`BatchConfig`, `FnName`, `AssumeAssertConfig`) hold the **static** choices: function names,
  boundary, trap policy, snapshot. Decoders are parameters, fixed per value type. How callers
  and hosts behave is not configuration: it is the set of plays.
* **Strategies**: `ofTraces` reads a component strategy through its named traces
  (`Silmaril.Wasi.Accept.Traces`). These are specification or any other strategies; nothing makes
  them compiled components.
* **Core modules**: `coreInterp` reads a module AST through `coreSeq`. Its configuration
  `CoreConfig` holds the profile, the admissible host set, the export name and the byte codec.
  `coreBytesInterp` first decodes bytes with silmaril-lean's binary decoder, and is `none` when
  they do not decode: that is not the empty system.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (Interp System Signed)
open Silmaril.Wasm.Component (Val)

variable {V : Type}

/-- The static configuration of the batch protocol. -/
structure BatchConfig where
  b : Boundary
  fns : BatchFns
  td : TrapDone

/-- **The batch protocol as an interpretation of trace sets.** -/
def batchInterp (decV : List Val → Option V) :
    Interp BatchConfig (Set (List WEv)) (fun _ => List (Signed V)) (fun _ => Unit) :=
  fun e T => some (Accepted T (importBatch e.b e.fns decV e.td))

/-- **The two-list check as an interpretation of trace sets**, configured by the export. -/
def seqInterp (decΓ decΔ : Val → Option (List V)) :
    Interp FnName (Set (List WEv)) (fun _ => List V) (fun _ => List V) :=
  fun f T => some (seqOf T (seqCheck f decΓ decΔ))

/-- The static configuration of the assume/assert protocol. -/
structure AssumeAssertConfig where
  b : Boundary
  fns : AssumeAssertFns
  snap : SnapshotAt

/-- **The assume/assert protocol as an interpretation of trace sets.** -/
def assumeAssertInterp (decV : List Val → Option V) :
    Interp AssumeAssertConfig (Set (List WEv)) (fun _ => List V × List V) (fun _ => Unit) :=
  fun e T => some (Accepted T (exportAssumeAssert e.b e.fns decV e.snap))

/-- Its sequent form: `Γ ⊢ Δ` iff the pair `(Γ, Δ)` is accepted. -/
def assumeAssertSeqInterp (decV : List Val → Option V) :
    Interp AssumeAssertConfig (Set (List WEv)) (fun _ => List V) (fun _ => List V) :=
  (assumeAssertInterp decV).map fun _ S Γ Δ => S (Γ, Δ) ()

/-- Read strategies through their named traces. -/
def ofTraces {Env : Type} {Ax C : Env → Type} {I X : Set FnName}
    (J : Interp Env (Set (List WEv)) Ax C) :
    Interp Env (Silmaril.Games.Strategy (nsig I) (nsig X)) Ax C :=
  J.comap fun σ => some (Accept.Traces σ)

/-- The static configuration of a core module's export read as a sequent relation. -/
structure CoreConfig where
  /-- The numerics profile. -/
  P : Silmaril.Wasm.Numerics.Profile
  /-- The admissible hosts. -/
  Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)
  /-- The export, `name(ptr: i32, len: i32) -> i32`. -/
  name : String
  /-- The byte codec of sequents. -/
  enc : List UInt8 → List UInt8 → Option (List UInt8)

/-- **A core module as an interpretation**: its export through the configured codec. -/
def coreInterp :
    Interp CoreConfig Silmaril.Wasm.Module (fun _ => List UInt8) (fun _ => List UInt8) :=
  fun e m => some (coreSeq e.P e.Hosts m e.name e.enc)

/-- **Bytes as an interpretation**: decode, then read the module; `none` when they do not
decode. -/
def coreBytesInterp :
    Interp CoreConfig ByteArray (fun _ => List UInt8) (fun _ => List UInt8) :=
  coreInterp.comap Silmaril.Wasm.Binary.Core.decode?

/-- The `MemberCheck` configuration: export `check`, codec `memberEnc`. -/
def memberConfig (P : Silmaril.Wasm.Numerics.Profile)
    (Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)) : CoreConfig :=
  ⟨P, Hosts, "check", memberEnc⟩

end Silmaril.Wasi.Consequence
