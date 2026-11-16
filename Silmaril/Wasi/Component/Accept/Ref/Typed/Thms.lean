module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public import Silmaril.Wasi.Component.Accept.Ref.Thms
import Silmaril.Proofs.Wasi.Component.Accept.RefTyped

/-! # Component acceptors on the reference machine, typed environment: theorems

* `acceptedTyped_accepted`, `acceptedExportTyped_acceptedExport`, `refTypedBytesSystem_le`: the
  typed notions are included in the untyped ones (the untyped ones also contain the spurious
  runs of ill-typed hosts).
* `recordsTyped_of_run`, `acceptedTyped_bytes`, `bytesOf?_bytesVal`: what the driver records, and
  `list<u8>` acceptance read through `bytesOf?`.
* `acceptRunTyped_sound`: the typed executable driver is sound for `AcceptedTyped`.
* `acceptedExportTyped_of_run`: an executable run at the right type proves `AcceptedExportTyped`.
* `refTypedBytesSystem_of_decode`, `refTypedBytesSystem_of_run`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon

section

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {prof : ProfileKind}
  {c : Syntax.Component E.Module} {w : List UInt8}

theorem acceptedTyped_accepted (h : AcceptedTyped prof c w) : Accepted prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.acceptedTyped_accepted h

theorem acceptedExportTyped_acceptedExport (h : AcceptedExportTyped prof c w) :
    AcceptedExport prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.acceptedExportTyped_acceptedExport h

theorem acceptRunTyped_sound (X : E.Exec) (o : Oracle E) {fuel : Nat}
    {calls : List (String × List Value.Val)} {st : AcceptSt}
    (h : acceptRunTyped X o fuel c calls = some st) (hw : [bytesVal w] ∈ st) :
    AcceptedTyped o.prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.acceptRunTyped_sound X o h hw

theorem recordsTyped_of_run (X : E.Exec) (o : Oracle E) {fuel : Nat}
    {ft : WIT.FuncType Empty RtId} {calls : List (String × List Value.Val)} {st : AcceptSt}
    (h : acceptRunTyped X o fuel c calls ft = some st) {args : List Value.Val} (hw : args ∈ st) :
    RecordsTyped ft o.prof c args :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.recordsTyped_of_run X o h hw

theorem acceptedTyped_bytes (h : AcceptedTyped prof c w) : AcceptedTypedBytes acceptFT prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.acceptedTyped_bytes h

theorem bytesOf?_bytesVal (w : List UInt8) : bytesOf? [bytesVal w] = some w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.bytesOf?_bytesVal w

theorem acceptedExportTyped_of_run (X : E.Exec) (o : Oracle E) {fuel fuel' : Nat}
    {r₁ : RunResult E AcceptSt o.State} {inst : InstId} {es : List (String × FuncId)}
    {f : FuncId} {ft : WIT.FuncType Empty RtId} {r : RunResult E AcceptSt o.State}
    (hi : (emb X).instantiateRun o fuel c [] (Silmaril.Wasm.Component.Reference.initConfig []) =
      some (r₁, inst, es))
    (hf : es.lookup "accept" = some f) (hft : funcFT? r₁.config f = some ft)
    (hty : argsTyped ft [bytesVal w] = true) (hres : ft.result = some (.prim .bool))
    (hc : (emb X).callTop o fuel' ⟨0⟩ f [bytesVal w] r₁.config = some r)
    (ho : callOutcome? ⟨0⟩ r = some (.resolved (some [.bool true]))) :
    AcceptedExportTyped o.prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.acceptedExportTyped_of_run X o hi hf hft hty hres hc ho

end

variable {prof : ProfileKind} {b : ByteArray} {w : List UInt8}

theorem refTypedBytesSystem_of_decode {a : RefAcceptor prof} (h : decodeValid b = some a) :
    refTypedBytesSystem prof b w ↔ AcceptedTyped prof a.comp w :=
  ⟨fun ⟨_, ha', hw⟩ => by
      obtain ⟨a'', h'', rfl⟩ := Option.map_eq_some_iff.mp ha'
      rw [h] at h''; cases h''; exact hw,
    fun hw => ⟨⟨a.comp⟩, by simp [h], hw⟩⟩

theorem refTypedBytesSystem_le : refTypedBytesSystem prof ≤ refBytesSystem prof :=
  fun _ _ ⟨a, ha, hw⟩ => by
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨a', ha', acceptedTyped_accepted hw⟩

theorem refTypedBytesSystem_of_run (o : Oracle Eng) {a : RefAcceptor o.prof}
    (hd : decodeValid b = some a) {fuel : Nat} {calls : List (String × List Value.Val)}
    {st : AcceptSt}
    (hr : acceptRunTyped (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) o fuel a.comp calls =
      some st)
    (hw : [bytesVal w] ∈ st) : refTypedBytesSystem o.prof b w :=
  (refTypedBytesSystem_of_decode hd).2 (acceptRunTyped_sound _ o hr hw)

end Silmaril.Wasi.Accept.Ref
