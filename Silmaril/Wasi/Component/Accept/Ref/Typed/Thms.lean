module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public import Silmaril.Wasi.Component.Accept.Ref.Thms
import Silmaril.Proofs.Wasi.Component.Accept.RefTyped

/-! # Component acceptors on the reference machine, typed environment: theorems

The generic policy theorems (`acceptedTyped_accepted`, `acceptRunTyped_sound`,
`recordsTyped_of_run`, `bytesSystem_of_run`, …) are in `Ref/Thms.lean`. Here:

* `acceptedExportTyped_acceptedExport`: typed exported acceptance implies the untyped one.
* `acceptedTyped_bytes`, `bytesOf?_bytesVal`: `list<u8>` acceptance read through `bytesOf?`.
* `acceptedExportTyped_of_run`: an executable run at the right type proves `AcceptedExportTyped`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon

section

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {prof : ProfileKind}
  {c : Syntax.Component E.Module} {w : List UInt8}

theorem acceptedExportTyped_acceptedExport (h : AcceptedExportTyped prof c w) :
    AcceptedExport prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.acceptedExportTyped_acceptedExport h

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

end Silmaril.Wasi.Accept.Ref
