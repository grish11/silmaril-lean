# Complete Elgot iteration of finite trace observations

Import [`Silmaril.Semantics.NondeterministicTrace.Thms`][api]. The log type is
any monoid. For words, use a free monoid with concatenation in execution
order. A finite trace monoid can supply a quotient homomorphism from words
to trace classes. The model requires only the monoid operations and the
homomorphism laws.

## Carriers and iteration

- `Finite W A` is `WriterT W SetM A`. An observation is a possible return
  value paired with its finite log. A recursive branch with no finite
  returning run contributes no observation.
- `Tagged W T A` is `ExceptT T (Finite W) A`. An observation is either a
  returned value or an explicitly supplied incomplete tag, paired with
  its finite log. An incomplete branch keeps its log and skips the
  continuation. The empty set yields no observation, while a tag with the
  identity log is an observable incomplete branch. A tag may be supplied at
  a checkpoint even when a separate branch continues.
- The existing [Elgot transformer instances][transformers] supply fixpoint,
  naturality, codiagonal and pure uniformity. `finiteElgot` and `taggedElgot`
  instantiate the [CALCO complete-Elgot adapter][calco] with total
  guardedness. Its Kleisli law bundle includes dinaturality.
- `Finite.mem_iter` identifies observations with finite state paths and
  products of the logs on their edges. `Tagged.mem_iter` does the same after
  the exception transformer classifies incomplete tags as terminal
  observations rather than recursive calls. Both `iter_eq_lfp` theorems
  identify the transformer iteration with the least fixed point of one
  actual Kleisli unfolding under pointwise set inclusion.

## Embeddings and quotients

`Tagged.resultsEmbedding` includes the finite-result model in the tagged
model. Its image consists of observations carrying successful values. It
preserves pure, bind, and iteration.

For both carriers, `mapLog h` takes the direct image by a monoid homomorphism
on the log and retains the return value or tag. Every finite path transports
by mapping its log factors. Conversely, each edge of a finite path in the
mapped body has a source witness with the same state transition. This is
why the direct image commutes with iteration even for a noninjective
quotient. The map also preserves pure and bind. `logEmbedding` packages an
injective homomorphism as an Elgot embedding. For a surjective homomorphism,
`logQuotient` identifies the target carrier with the kernel quotient of the
map.

## Divergence and finite observations

An uninstrumented silent self-loop has empty least behavior even in the
tagged model. A loop that emits a log `w` and explicitly offers an incomplete
checkpoint at the start of each step has exactly the incomplete observations
`1, w, w², …`. The [regression][regression] checks both cases. It also
checks that a body with one nondeterministic choice of a finite power and
no recursive edges gives the same observations as the checkpoint loop.

The last example is an obstruction to recovering actual infinite runs from
the union of finite checkpoints. Infinite-run semantics needs paths or a
compatibility condition that keeps observations from one branch together.
It also needs a choice about silent divergence and an iteration law for
how finite and infinite outcomes interact. The [printing hang model][hangs]
gives an existing path-based Elgot instance for nonempty sets of printing
traces with finite hangs and infinite streams. Transporting such an
iteration to concurrent quotient ideals would require a run correspondence
and compatibility of infinite accumulation with sequencing and the quotient
map. The maps proved here operate on finite log observations.

## Reproduce

```sh
lake build --wfail +Silmaril.Semantics.NondeterministicTrace.Thms \
  +Silmaril.Proofs.Semantics.NondeterministicTrace.Regression
make check CHECK_TARGETS='+Silmaril.Semantics.NondeterministicTrace.Thms +Silmaril.Proofs.Semantics.NondeterministicTrace.Regression'
```

[api]: ../../Silmaril/Semantics/NondeterministicTrace/Thms.lean
[transformers]: ../../Silmaril/Semantics/ElgotMonads/Thms.lean
[calco]: ../../Silmaril/Semantics/Calco2019/CompleteElgot/Thms.lean
[hangs]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/HangTraces/Laws/Thms.lean
[regression]: ../../Silmaril/Proofs/Semantics/NondeterministicTrace/Regression.lean
