module

public import Silmaril.Wasm.Interp.Closed.Defs
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Interp.Closed

/-!
# Closed modules through the native interpreter: theorems

For a module `m` with no imports, the four hypotheses of `Silmaril.Wasm.Interp.native_adequacy`
become one Boolean check `callOk m a vs = true`, which the kernel evaluates
(`decide +kernel`). With a terminating interpreter run it gives the exact Core 3.0 behaviour set
at **every** numeric profile:

```lean
example (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (Closed.store m) a vs = {.returns [Val.i32 7]} :=
  Closed.behaviours_eq (fuel := 20) (by decide +kernel) (by decide +kernel) P
```

* `instantiate` (`instantiate_of_prepare` for a given allocation): `closed? m` makes `store m` the store of `m`'s Core 3.0 instantiation in the
  empty store, at every profile and host; `storeOk`: it is typed;
* `adequacy`: under `callOk m a vs`, the Core behaviours of calling `a` with `vs` are the native
  interpreter's (`nbeh`), at every profile;
* **`behaviours_eq`**: if moreover `run m fuel a vs = some b`, the Core behaviours are exactly
  `{b}`: the call returns (or traps, or throws) as the run did, and nothing else happens — no
  other result, no divergence;
* `nbeh_eq_singleton`, `invokeRun_mono`: the two facts about the interpreter this needs, for any
  store.

What a failed check means is stated in `Silmaril.Wasm.Interp.Closed.Defs` (partiality);
`Silmaril.Wasm.Interp.Closed.Examples` exercises a return, a trap, an unsupported module and a
run that needs more fuel. Proofs: `Silmaril.Proofs.Wasm.Interp.Closed`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.Closed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- A module that validates without imports and that `prepare?` allocates without a start
function instantiates to the allocation, at every profile and host (the form of `instantiate`
for a given allocation `p`). -/
theorem instantiate_of_prepare {m : Module} {p : Config Empty × Option FuncIdx}
    (hv : ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true)
    (hp : prepare? evalConst? ({} : Store Empty) m [] = some p) (hst : p.2 = none)
    (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) m [] p.1 :=
  Silmaril.Proofs.Wasm.Interp.Closed.instantiate_of_prepare hv hp hst P host

/-- The store of such an instance is typed. -/
theorem storeOk_of_prepare {m : Module} {p : Config Empty × Option FuncIdx}
    (hv : ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true)
    (hp : prepare? evalConst? ({} : Store Empty) m [] = some p) (hst : p.2 = none) :
    StoreOk p.1.store :=
  Silmaril.Proofs.Wasm.Interp.Closed.storeOk_of_prepare hv hp hst

/-- **`closed? m` instantiates `m` to `prep m`**, at every profile and host. -/
theorem instantiate {m : Module} (h : closed? m = true) (P : Numerics.Profile)
    (host : HostSemantics Empty) : Instantiate P host ({} : Store Empty) m [] (prep m).1 :=
  Silmaril.Proofs.Wasm.Interp.Closed.instantiate h P host

/-- The instance's store is typed. -/
theorem storeOk {m : Module} (h : closed? m = true) : StoreOk (store m) :=
  Silmaril.Proofs.Wasm.Interp.Closed.storeOk h

/-- The hypotheses of `native_adequacy`, from the Boolean check. -/
theorem callOk_spec {m : Module} {a : Nat} {vs : List Val} (h : callOk m a vs = true) :
    StoreOk (store m) ∧ Binaryen.NativeFuncsOk (store m).funcs ∧ StoreChk (store m).funcs ∧
      InvokeOk (store m) a vs :=
  let ⟨hn, hok⟩ := Silmaril.Proofs.Wasm.Interp.Closed.callOk_spec h
  let ⟨hc, hF, hS⟩ := Silmaril.Proofs.Wasm.Interp.Closed.nativeCheck_spec hn
  ⟨storeOk hc, hF, hS, hok⟩

/-- **Native adequacy for a checked call of a closed module**, at every profile. -/
theorem adequacy {m : Module} {a : Nat} {vs : List Val} (h : callOk m a vs = true)
    (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (store m) a vs = Binaryen.nbeh (store m) a vs :=
  Silmaril.Proofs.Wasm.Interp.Closed.adequacy h P

/-- More fuel never changes a result of `invokeRun`. -/
theorem invokeRun_mono {H : Type} {n n' : Nat} (hle : n ≤ n') {s : Store H} {a : Nat}
    {vs : List Val} {r : Store H × Binaryen.Flow} (h : Binaryen.invokeRun n s a vs = some r) :
    Binaryen.invokeRun n' s a vs = some r :=
  Silmaril.Proofs.Wasm.Interp.Closed.invokeRun_mono hle h

/-- The native behaviours of a terminating invocation are its single result. -/
theorem nbeh_eq_singleton {H : Type} {s : Store H} {a : Nat} {vs : List Val} {n : Nat}
    {b : Behaviour Val} (h : ((Binaryen.invokeRun n s a vs).bind fun r => Binaryen.flowBeh r.2) =
      some b) : Binaryen.nbeh s a vs = {b} :=
  Silmaril.Proofs.Wasm.Interp.Closed.nbeh_eq_singleton h

/-- **The Core 3.0 behaviours of a checked call are exactly the result of one terminating
interpreter run**, at every profile. -/
theorem behaviours_eq {m : Module} {a : Nat} {vs : List Val} {fuel : Nat} {b : Behaviour Val}
    (h : callOk m a vs = true) (hr : run m fuel a vs = some b) (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (store m) a vs = {b} :=
  Silmaril.Proofs.Wasm.Interp.Closed.behaviours_eq h hr P

end Silmaril.Wasm.Interp.Closed
