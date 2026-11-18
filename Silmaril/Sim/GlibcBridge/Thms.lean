module

public import Silmaril.Proofs.Sim.GlibcBridge.Hello

/-!
# glibc functions as Wasm imports: results

Definitions in `Silmaril.Sim.GlibcBridge.Defs`; proofs in `Silmaril.Proofs.Sim.GlibcBridge.Hello`;
runtime in `examples/wasm-sim/glibc-bridge`.

* **`lrun_mono`** (assume-guarantee): linked runs with import implementations meeting their
  contracts are linked runs with the contracts; `linkObs_mono` on observables.
* **`enc_extStore`**: the import call (`ext`) is sound for the System V call boundary: the store
  after it encodes `rax := result`, scratch registers arbitrary, flags undefined, `rip += len`.
* **`ghello_lrun`** / **`ghello_run_of`**: the linked runs of the glibc hello's `main` with a
  `puts` meeting `putsC1` (= `Silmaril.Libc.putsGlibc` on bytes, non-empty output) and
  `exitC` produce exactly the WASI hello's observables.
* **`ghello_refines`**, **`ghello_equiv`**: the composition theorem — every implementation
  meeting the `puts` contract gives a linked whole refining the WASI hello; if it also admits
  every output, the linked whole ≡ the WASI hello (`ElfWasiEquiv … helloWasi S1`).
* **`ghello_equiv_contract`**: program ⊗ `putsC1` ≡ WASI hello.
* **`putsImpl_meets`**: `glibc.wat`'s `puts` (one `fd_write`, result `|s| + 1` or `EOF`)
  meets `putsC1` for every string; **`ghello_equiv_impl`**: linked with it, ≡ WASI hello.
* **`ghello_equiv_static`**: the linked glibc hello ≡ the static hello process under LPS's
  Linux model (with `Silmaril.Sim.WasiBridge.G.hello_equiv_lps`).
-/

/-- info: 'Silmaril.Sim.GlibcBridge.ghello_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.ghello_equiv

/-- info: 'Silmaril.Sim.GlibcBridge.ghello_equiv_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.ghello_equiv_impl

/-- info: 'Silmaril.Sim.GlibcBridge.ghello_equiv_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.ghello_equiv_static

/-- info: 'Silmaril.Sim.GlibcBridge.lrun_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.lrun_mono
