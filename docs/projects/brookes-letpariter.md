# LetParIter over finite Brookes SC traces

Import `Silmaril.SSA.Isotope.BrookesLetParIter.Thms`. The theorem
`Silmaril.Isotope.BrookesLetParIter.sound` instantiates the generic
`LetParIter.sound` on one instruction signature. It gives equality of
closed behaviors, including their complete open words and terminal values,
for every generated equation at its specified typing derivations and every
valuation. Singleton initial-store, final-store and return observations
therefore agree as well. The same equations hold for the shared tier
interpreter by `Silmaril.Isotope.BrookesLetParIter.interpret_sound`.

The world has two threads, one natural-number cell, one mutex, and no
external operations. Loads, stores, acquire, and release use the
[fixed-world SC primitives][primitives]. Pairing uses closed shuffle and
iteration uses the omega union of finite completed approximants
from the [Brookes model][iteration].

- The `InstructionModel` has a pure identity on words. Its
  `denote_pure` field proves agreement with monadic return at effect
  bottom. `pure_instruction_iff` shows that identity is the sole
  instruction annotated bottom. Every load, store, acquire and release
  has the other effect, even when an individual execution leaves the
  store unchanged.
- The empty type is interpreted by `Empty`. Eliminating it after a
  computation produces bottom by `abort_empty`. The generic soundness
  theorem requires no additional abort operation or law in its interface.
- The equation derivation carries the syntactic purity and native
  uniformity guards where required. The soundness theorem uses those
  derivations and the checked `LawfulElgotMonad` and `ParallelPairing`
  structures. No additional global loop guard is a model hypothesis.
- Acquire completes in isolation from a free mutex and has no singleton
  completion from an occupied mutex. Release completes in isolation for
  the owner and has no singleton completion for a nonowner. The open
  behavior can still be used in a schedule that changes the store before
  the mutex operation.

The [regression][regression] interprets a write in parallel with a
returning load loop. It checks a closed completion where the load sees
the old word before the other thread writes, and uses the instantiated
soundness theorem to swap the two branches and their result positions.

This is finite completed SC. The observation model has no fair infinite
traces, divergent prefixes, or must-termination observations.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.Isotope.BrookesLetParIter.Thms +Silmaril.Proofs.SSA.Isotope.BrookesLetParIter.Regression LetParIterTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/BrookesLetParIterAxioms.lean
```

[primitives]: brookes-sc-concrete.md
[iteration]: sc-brookes-iteration.md
[regression]: ../../Silmaril/Proofs/SSA/Isotope/BrookesLetParIter/Regression.lean
