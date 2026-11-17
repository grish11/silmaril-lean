module

public import Silmaril.Proofs.Sim.GlibcBridge.BytesConv

/-!
# The glibc hello's actual bytes on GM: results

Definitions in `Silmaril.Sim.GlibcBridge.Bytes.Defs`; proofs in
`Silmaril.Proofs.Sim.GlibcBridge.{Bytes,BytesConv}`.

* **`emitB_sound`**: the added methods (`endbr64`, RIP-relative `lea`) with GM's are sound for
  `Silmaril.X86.Ext.exec`; **`jmpInd_sound`**: the `jmp *[rip+d]` step is `Ext9.execNew`'s.
* **`tabAt_ghello`**: the code table is what the bytes of `main` and `puts@plt` decode to.
* **`ghelloB_run`** / **`ghelloB_run_of`**: dispatcher runs of the actual bytes with a `puts`
  meeting `putsC1` have exactly the WASI hello's observables.
* **`ghelloB_equiv`**: the actual linked bytes ≡ the WASI hello, relative to the `puts` contract;
  **`ghelloB_equiv_impl`**: with the bytes in memory and `glibc.wat`'s `puts`.
-/

/-- info: 'Silmaril.Sim.GlibcBridge.ghelloB_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.ghelloB_equiv

/-- info: 'Silmaril.Sim.GlibcBridge.ghelloB_equiv_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.ghelloB_equiv_impl
