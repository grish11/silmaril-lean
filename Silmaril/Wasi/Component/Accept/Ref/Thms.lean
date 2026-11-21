module

public import Silmaril.Wasi.Component.Accept.Ref.Defs
public import Silmaril.Logic.Consequence.Acceptor.Thms
public import Silmaril.Wasm.Component.Reference.Thms
import Silmaril.Proofs.Wasi.Component.Accept.Ref

/-! # Component acceptors on the reference machine: theorems

Once for every environment policy `P` and `accept` type `ft`:

* `recordsWith_of_run`: every argument list the executable driver `acceptRunWith` records is
  recorded in `RecordsWith P ft`, at the oracle's profile, for every core engine and
  interpreter. The executable run is a relational run of the machine (`hostStep?_sound`,
  `Machine.run_sound`, `Conformance.callUntil_sound`); after instantiation it uses only moves
  of `P` (each invoke passed `P.check`, sound by `P.check_sound`). `acceptRunWith_sound` is
  its `list<u8>` case.
* `RecordsWith.mono`, `AcceptedWith.mono`, `bytesSystemWith_mono`: a larger policy records and
  accepts more. `EnvPolicy.typed_le_untyped`, so `acceptedTyped_accepted` and
  `bytesSystem_le_untyped`.
* `bytesSystemWith_iff`, `bytesSystemWith_of_decode`, `bytesSystemWith_of_decode_none`,
  `bytesSystemWith_of_run`: the bytes system is acceptance of the decoded, validated
  component; an executable run of a decoded component that records `w` puts `w` in it.

The untyped (`acceptRun_sound`, …) and typed (`acceptRunTyped_sound`, `recordsTyped_of_run`, …)
names are these instances. `accepted_iff` and `acceptedTyped_iff` restate the instances in
full (`Iff.rfl`). `acceptedExport_of_run`: the exported shape, from an executable run.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon

/-! ## Policies -/

theorem EnvPolicy.typed_le_untyped {E : CoreEngine} :
    (EnvPolicy.typed : EnvPolicy E) ≤ EnvPolicy.untyped :=
  fun _ _ _ _ h => h.1

section

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {P Q : EnvPolicy E}
  {ft : WIT.FuncType Empty RtId} {prof : ProfileKind} {c : Syntax.Component E.Module}
  {args : List Value.Val} {w : List UInt8}

theorem RecordsWith.mono (hPQ : P ≤ Q) (h : RecordsWith P ft prof c args) :
    RecordsWith Q ft prof c args :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.recordsWith_mono hPQ h

theorem AcceptedWith.mono (hPQ : P ≤ Q) (h : AcceptedWith P prof c w) : AcceptedWith Q prof c w :=
  RecordsWith.mono hPQ h

theorem acceptedTyped_accepted (h : AcceptedTyped prof c w) : Accepted prof c w :=
  AcceptedWith.mono EnvPolicy.typed_le_untyped h

/-- `Accepted` in full: the linked instantiation, then untyped environment moves only, records
`[list<u8> w]`. -/
theorem accepted_iff : Accepted prof c w ↔ ∃ tr₀ m₁ inst es tr m₂,
    Steps prof noReady dispatch initCfg (.host (.run (acceptLinkedProg c)) :: tr₀) m₁ ∧
    (∀ ev, Label.host ev ∉ tr₀) ∧
    (traceObs tr₀).findSome? decodeInstantiated? = some (inst, es) ∧
    Steps prof noReady dispatch m₁ tr m₂ ∧ (∀ l ∈ tr, EnvLabel es l) ∧
    [bytesVal w] ∈ m₂.host :=
  Iff.rfl

/-- `AcceptedTyped` in full: as `accepted_iff`, with typed environment moves. -/
theorem acceptedTyped_iff : AcceptedTyped prof c w ↔ ∃ tr₀ m₁ inst es tr m₂,
    Steps prof noReady dispatch initCfg (.host (.run (acceptLinkedProg c)) :: tr₀) m₁ ∧
    (∀ ev, Label.host ev ∉ tr₀) ∧
    (traceObs tr₀).findSome? decodeInstantiated? = some (inst, es) ∧
    Steps prof noReady dispatch m₁ tr m₂ ∧ (∀ l ∈ tr, TypedEnvLabel m₁ es l) ∧
    [bytesVal w] ∈ m₂.host :=
  Iff.rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The untyped moves, explicitly. -/
theorem envLabel_invoke {es : List (String × FuncId)} {k : CallId} {f : FuncId}
    {as : List Value.Val} : EnvLabel (E := E) es (.host (.invoke k f as)) ↔ f ∈ es.map Prod.snd :=
  Iff.rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The typed moves, explicitly. -/
theorem typedEnvLabel_invoke {m₁ : Config E AcceptSt} {es : List (String × FuncId)} {k : CallId}
    {f : FuncId} {as : List Value.Val} : TypedEnvLabel m₁ es (.host (.invoke k f as)) ↔
      f ∈ es.map Prod.snd ∧ ∃ ft, funcFT? m₁ f = some ft ∧ argsTyped ft as = true :=
  Iff.rfl

end

/-! ## The executable driver -/

section

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec) (o : Oracle E)
  {fuel : Nat} {c : Syntax.Component E.Module} {calls : List (String × List Value.Val)}
  {ft : WIT.FuncType Empty RtId} {st : AcceptSt} {args : List Value.Val} {w : List UInt8}

/-- **Soundness of the executable driver**, for every policy `P` and `accept` type `ft`. -/
theorem recordsWith_of_run (P : EnvPolicy E) (h : acceptRunWith X o P fuel c calls ft = some st)
    (hw : args ∈ st) : RecordsWith P ft o.prof c args :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.recordsWith_of_run X o P h hw

theorem acceptRunWith_sound (P : EnvPolicy E) (h : acceptRunWith X o P fuel c calls = some st)
    (hw : [bytesVal w] ∈ st) : AcceptedWith P o.prof c w :=
  recordsWith_of_run X o P h hw

theorem acceptRun_sound (h : acceptRun X o fuel c calls = some st) (hw : [bytesVal w] ∈ st) :
    Accepted o.prof c w :=
  acceptRunWith_sound X o _ h hw

theorem acceptRunTyped_sound (h : acceptRunTyped X o fuel c calls = some st)
    (hw : [bytesVal w] ∈ st) : AcceptedTyped o.prof c w :=
  acceptRunWith_sound X o _ h hw

theorem recordsTyped_of_run (h : acceptRunTyped X o fuel c calls ft = some st) (hw : args ∈ st) :
    RecordsTyped ft o.prof c args :=
  recordsWith_of_run X o _ h hw

end

/-! ## Exported `accept` -/

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

/-! ## Bytes -/

section

variable {P Q : EnvPolicy Eng} {prof : ProfileKind} {b : ByteArray} {w : List UInt8}

theorem bytesSystemWith_iff : bytesSystemWith P prof b w ↔
    ∃ a : RefAcceptor prof, decodeValid b = some a ∧ AcceptedWith P prof a.comp w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.bytesSystemWith_iff

theorem bytesSystemWith_of_decode {a : RefAcceptor prof} (h : decodeValid b = some a) :
    bytesSystemWith P prof b w ↔ AcceptedWith P prof a.comp w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.bytesSystemWith_of_decode h

/-- Bytes that do not decode on REF, or do not validate, prove nothing. -/
theorem bytesSystemWith_of_decode_none (h : decodeValid (prof := prof) b = none) :
    ¬ bytesSystemWith P prof b w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.bytesSystemWith_of_decode_none h

theorem bytesSystemWith_mono (hPQ : P ≤ Q) : bytesSystemWith P prof ≤ bytesSystemWith Q prof :=
  fun _ _ h => bytesSystemWith_iff.2 <|
    let ⟨a, ha, hw⟩ := bytesSystemWith_iff.1 h; ⟨a, ha, AcceptedWith.mono hPQ hw⟩

/-- The default (typed) bytes system is included in the untyped one. -/
theorem bytesSystem_le_untyped : bytesSystem prof ≤ bytesSystemUntyped prof :=
  bytesSystemWith_mono EnvPolicy.typed_le_untyped

/-- **An executable run proves acceptance of bytes**, in environment `P`. -/
theorem bytesSystemWith_of_run (P : EnvPolicy Eng) (o : Oracle Eng) {a : RefAcceptor o.prof}
    (hd : decodeValid b = some a) {fuel : Nat} {calls : List (String × List Value.Val)}
    {st : AcceptSt}
    (hr : acceptRunWith (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) o P fuel a.comp calls =
      some st)
    (hw : [bytesVal w] ∈ st) : bytesSystemWith P o.prof b w :=
  (bytesSystemWith_of_decode hd).2 (acceptRunWith_sound _ o P hr hw)

/-- **A typed executable run proves acceptance of bytes** in the default system. -/
theorem bytesSystem_of_run (o : Oracle Eng) {a : RefAcceptor o.prof}
    (hd : decodeValid b = some a) {fuel : Nat} {calls : List (String × List Value.Val)}
    {st : AcceptSt}
    (hr : acceptRunTyped (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) o fuel a.comp calls =
      some st)
    (hw : [bytesVal w] ∈ st) : bytesSystem o.prof b w :=
  bytesSystemWith_of_run _ o hd hr hw

/-! ### Deprecated names -/

@[deprecated "use `bytesSystemWith_iff` (generic in the environment policy)" (since := "2026-11-16")]
theorem refBytesSystem_iff : bytesSystemUntyped prof b w ↔
    ∃ a : RefAcceptor prof, decodeValid b = some a ∧ Accepted prof a.comp w :=
  bytesSystemWith_iff

@[deprecated "use `bytesSystemWith_of_decode` (generic in the environment policy)" (since := "2026-11-16")]
theorem refBytesSystem_of_decode {a : RefAcceptor prof} (h : decodeValid b = some a) :
    bytesSystemUntyped prof b w ↔ Accepted prof a.comp w :=
  bytesSystemWith_of_decode h

@[deprecated "use `bytesSystemWith_of_decode_none` (generic in the environment policy)" (since := "2026-11-16")]
theorem refBytesSystem_of_decode_none (h : decodeValid (prof := prof) b = none) :
    ¬ bytesSystemUntyped prof b w :=
  bytesSystemWith_of_decode_none h

@[deprecated "use `bytesSystemWith_of_run` (generic in the environment policy)" (since := "2026-11-16")]
theorem refBytesSystem_of_run (o : Oracle Eng) {a : RefAcceptor o.prof}
    (hd : decodeValid b = some a) {fuel : Nat} {calls : List (String × List Value.Val)}
    {st : AcceptSt}
    (hr : acceptRun (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) o fuel a.comp calls =
      some st)
    (hw : [bytesVal w] ∈ st) : bytesSystemUntyped o.prof b w :=
  bytesSystemWith_of_run _ o hd hr hw

@[deprecated "use `bytesSystemWith_of_decode` (generic in the environment policy)" (since := "2026-11-16")]
theorem refTypedBytesSystem_of_decode {a : RefAcceptor prof} (h : decodeValid b = some a) :
    bytesSystem prof b w ↔ AcceptedTyped prof a.comp w :=
  bytesSystemWith_of_decode h

@[deprecated bytesSystem_le_untyped (since := "2026-11-16")]
theorem refTypedBytesSystem_le : bytesSystem prof ≤ bytesSystemUntyped prof :=
  bytesSystem_le_untyped

@[deprecated bytesSystem_of_run (since := "2026-11-16")]
theorem refTypedBytesSystem_of_run (o : Oracle Eng) {a : RefAcceptor o.prof}
    (hd : decodeValid b = some a) {fuel : Nat} {calls : List (String × List Value.Val)}
    {st : AcceptSt}
    (hr : acceptRunTyped (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) o fuel a.comp calls =
      some st)
    (hw : [bytesVal w] ∈ st) : bytesSystem o.prof b w :=
  bytesSystem_of_run o hd hr hw

end

end Silmaril.Wasi.Accept.Ref
