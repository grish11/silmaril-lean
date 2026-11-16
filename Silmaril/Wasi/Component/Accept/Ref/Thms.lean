module

public import Silmaril.Wasi.Component.Accept.Ref.Defs
public import Silmaril.Logic.Consequence.Acceptor.Thms
public import Silmaril.Wasm.Component.Reference.Thms
import Silmaril.Proofs.Wasi.Component.Accept.Ref

/-! # Component acceptors on the reference machine: theorems

* `acceptRun_sound`: every byte list the executable driver records is accepted (`Accepted`),
  at the oracle's profile, for every core engine and interpreter. The executable run is a
  relational run of the machine (`hostStep?_sound`, `Machine.run_sound`,
  `Conformance.callUntil_sound`). After instantiation it uses only invokes of exported
  functions and ticks (`EnvLabel`).
* `acceptedExport_of_run`: the exported shape, from an executable run.
* `refBytesSystem_iff`, `refBytesSystem_of_decode`, `refBytesSystem_of_decode_none`: the bytes
  system is acceptance of the decoded, validated component.
* `refBytesSystem_of_run`: an executable run of a decoded component that records `w` puts `w`
  in the bytes system. This is how concrete binaries are shown to accept a byte string.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon

theorem acceptRun_sound {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec)
    (o : Oracle E) {fuel : Nat} {c : Syntax.Component E.Module}
    {calls : List (String × List Value.Val)} {st : AcceptSt}
    (h : acceptRun X o fuel c calls = some st) {w : List UInt8} (hw : [bytesVal w] ∈ st) :
    Accepted o.prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.acceptRun_sound X o h hw

/-- **An executable run proves exported acceptance**: instantiate with no imports, call the export
`"accept"` on `w`, and the call resolves with `true`. -/
theorem acceptedExport_of_run {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)]
    (X : E.Exec) (o : Oracle E) {fuel fuel' : Nat} {c : Syntax.Component E.Module}
    {w : List UInt8} {r₁ : RunResult E AcceptSt o.State} {inst : InstId}
    {es : List (String × FuncId)} {f : FuncId} {r : RunResult E AcceptSt o.State}
    (hi : (emb X).instantiateRun o fuel c [] (Silmaril.Wasm.Component.Reference.initConfig []) =
      some (r₁, inst, es))
    (hf : es.lookup "accept" = some f)
    (hc : (emb X).callTop o fuel' ⟨0⟩ f [bytesVal w] r₁.config = some r)
    (ho : callOutcome? ⟨0⟩ r = some (.resolved (some [.bool true]))) :
    AcceptedExport o.prof c w :=
  Silmaril.Wasm.Component.Reference.exportBehaviours_of_run (emb X) o [] hi hf hc ho

variable {prof : ProfileKind} {b : ByteArray} {w : List UInt8}

theorem refBytesSystem_iff :
    refBytesSystem prof b w ↔ ∃ a : RefAcceptor prof, decodeValid b = some a ∧ Accepted prof a.comp w :=
  Iff.rfl

theorem refBytesSystem_of_decode {a : RefAcceptor prof} (h : decodeValid b = some a) :
    refBytesSystem prof b w ↔ Accepted prof a.comp w :=
  Silmaril.Consequence.System.ofDecoder_of_eq_some id h w

/-- Bytes that do not decode on REF, or do not validate, prove nothing. -/
theorem refBytesSystem_of_decode_none (h : decodeValid (prof := prof) b = none) :
    ¬ refBytesSystem prof b w :=
  Silmaril.Consequence.System.ofDecoder_of_eq_none id h w

/-- **An executable run proves acceptance of bytes.** -/
theorem refBytesSystem_of_run (o : Oracle Eng) {a : RefAcceptor o.prof}
    (hd : decodeValid b = some a) {fuel : Nat} {calls : List (String × List Value.Val)}
    {st : AcceptSt}
    (hr : acceptRun (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) o fuel a.comp calls =
      some st)
    (hw : [bytesVal w] ∈ st) : refBytesSystem o.prof b w :=
  (refBytesSystem_of_decode hd).2 (acceptRun_sound _ o hr hw)

end Silmaril.Wasi.Accept.Ref
