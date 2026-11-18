module

public import Silmaril.Sim.Institution.Defs
public import Silmaril.Proofs.Sim.Institution.Transfer

/-!
# The institution of simulators: what is proved (header)

PROVED in `Defs` (needed to build the institution): `sat_map_iff` (the satisfaction
condition), `Sen.map_id`, `Sen.map_comp`, `Mod.reduct_id`, `Mod.reduct_comp`, the functor laws
of `functor` and of the certified institution; so `inst V` and `certInst V` are institutions
(`Silmaril.Inst.Institution₁₁`).

PROVED here (proofs in `Silmaril/Proofs/Sim/Institution/Transfer.lean`, names in
`Silmaril.Sim.Institution`):

* `sat_of_hom`: model morphisms (soundness) preserve upward-closed angelic sentences;
  `sat_of_complete`: complete simulators preserve demonic sentences;
* **`transfer`** (headline; `transfer_inst` in the facade's `⊨[inst V]` notation): a sound
  simulator over `S`, a reference over `T`, a derived signature morphism `σ : S → T`;
  what the simulator satisfies, the reference satisfies after translation along `σ`;
  `transfer_demonic` (complete simulators, demonic sentences); `transfer_exact` (exact
  simulators, every angelic sentence, guards arbitrary); `sat_angelic_of_demonic`
  (a Wasm-style partial-correctness proof plus progress gives the angelic sentence);
* `transferSemi : SemiComorphism (inst V) (certInst V)`: the transfer as a facade
  semi-comorphism (backward direction, class `Sen.AngelicMono`);
* linking and structured specifications: `link` (assume-guarantee over opaque callees, then
  substitution of their bodies by a signature morphism), `entails_map` (translation),
  `entails_mono` (union);
* reductions (`Reduction`): `self`, `trans` (composition of a reduction DAG), `mono`,
  `transfer` (ISA problem → simulator problem + soundness), `link` (caller entailment + one
  problem per callee), `perCmd` (soundness → one problem per simulator method), `chain`
  (across the simulator lattice), `equiv` (G ≡ M representation equivalence), `accessors`
  (G ≡ M → one problem per accessor kind, `AccessorAgrees`).

Not proved: anything about a concrete Wasm module; the x86 instance is
`Silmaril.Sim.X86.GInst` (`docs/projects/wasm-sim.md`). No `sorry`, axiom or `Task` here.
-/
