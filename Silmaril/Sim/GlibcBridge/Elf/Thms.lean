module

public import Silmaril.Proofs.Sim.GlibcBridge.Elf

/-!
# The pinned glibc-linked hello under the eager loader: results

* **`got_puts`**: under `EagerLoaded ghelloLinkMap`, `GOT[puts]` (`0x404000`) holds the foreign
  address `putsF` (from `Silmaril.Sim.GlibcBridge.Link.got_word` and the pinned file's relocations).
* `plt_loaded`, `main_loaded`, `cstr_msg`: the code bytes and the string, from the loader relation.
* **`ghello_e2e`**, **`ghello_e2e_impl`**: the end-to-end statement. Trusted (hypotheses):
  `EagerLoaded ghelloLinkMap` (the loader; the file by its sha256), the guest-load import
  answering by memory, `StartAtMain` (the start-up contract,
  `Silmaril.Sim.GlibcBridge.Start.Defs`), and the `puts` implementation's contract.
-/

/-- info: 'Silmaril.Sim.GlibcBridge.ghello_e2e_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.GlibcBridge.ghello_e2e_impl
