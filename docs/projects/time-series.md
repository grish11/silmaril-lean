# Time series

Import `Silmaril.Data.TimeSeries` for typed observations, curve candidates, sampling,
additive noise, exact finite operations, quantization, and position and velocity compatibility.
The [example](../../Silmaril/Data/TimeSeries/Examples.lean) reads a typed relational
table with natural-number timestamps and integer measurements, decodes the columns to
reals, and proves that the observations fit an affine curve with unit additive error.
It checks both samples at the endpoints of a closed window and evaluates the forward
slope of the recorded data.

## From rows to observations

`Series n Time Value` has one observation at each index of `Fin n`.
`Series.ofTable table timeColumn valueColumn` selects two typed columns.
`Series.ofAlignedColumns` gives the same observations from the aligned column
representation. These adapters retain source order and repeated timestamps.
Use `mapTime` and `mapValue` to convert either axis, and `timestamps` and `values`
to pass the resulting columns to operations. Operations that depend on timestamp
order have their own contracts. For example, slope is undefined at an equal-time
pair. Interpolation can bracket ascending and descending pairs and gives priority
to the first exact timestamp match.
[Relational adapter](../../Silmaril/Data/TimeSeries/Relational/Thms.lean)
· [Operations](../../Silmaril/Data/TimeSeries/Operations/Defs.lean)

`Series.sample times f` records a supplied schedule and the exact evaluations of
`f`. Its value column is `Operations.sampleAt times f`. Use `series.addNoise ε`
to add one value error per index at the same recorded timestamps. Noise laws
push forward the joint vector of errors to the value column of this perturbed
series. The schedule is fixed, and errors at different indices can be dependent. With a
probability prior and a Markov noise kernel, the random observation law is a
probability measure. Mathlib's joint-law construction returns the zero measure
when the prior or kernel fails the s-finiteness requirement.
[Sampling](../../Silmaril/Data/TimeSeries/Sampling/Thms.lean)
· [Noise bridge](../../Silmaril/Data/TimeSeries/Sampling/Noise/Thms.lean)

## Candidate curves

Create a metric error model with `ErrorModel.ofDecode decodeTime decodeValue`
or provide two custom nonnegative losses. Each candidate needs one valid latent
schedule within both the time and value budgets. Each component of
`seriesError` is the maximum of its loss over the samples. `validTimes` can
constrain the entire schedule, and the optional eligibility test can depend on
the observed data, for example by selecting a speed bound. Under metric losses,
`exactCandidates` is the zero-budget case. For a `K`-Lipschitz candidate,
`recorded_value_error_le` bounds the error at the decoded recorded time by the
value budget plus `K` times the time budget.
[Error and candidate laws](../../Silmaril/Data/TimeSeries/Thms.lean)

`continuousCandidates` and `smoothCandidates` work with the parametrized
`Curves.OpenContinuous` and `Curves.OpenSmooth` bundles. For a closed window,
use `windowContinuousCandidates` or `windowSmoothCandidates` with the corresponding
window bundle. The latent schedule must lie in the interval, including its endpoints.
A recorded timestamp outside the interval can still pass if its time loss fits the
budget. Smooth windows require positive length and use the interval manifold at
the boundary. Candidate membership uses the actual time parametrization.
`Series.DerivativeCompatible` checks position and velocity in a real normed vector
space at specified latent times and uses the ordinary real-domain derivative.
[Curve candidates](../../Silmaril/Data/TimeSeries/CurveCandidates/Thms.lean)
· [Curves](../../Silmaril/Data/TimeSeries/Curves/Thms.lean)
· [Kinematics](../../Silmaril/Data/TimeSeries/Kinematics/Thms.lean)

## Quantized recordings

`Quantization.uniformSeries` rounds each original time to an integer grid index,
evaluates the signal at the decoded grid time, and rounds the value to its own
integer grid index. Use the two grid decoders with `ErrorModel.ofDecode`.
`Quantization.uniformSeries_mem_candidates` admits the original function when
its schedule is valid and it meets the eligibility and Lipschitz conditions.
The time budget is half a time step. The latent-time value budget is half a
value step plus the Lipschitz constant times the time budget.

`Quantization.mem_candidates_of_recorded_error` also accepts other decoders and
bounds measured at the decoded stored times. It transfers the value bound
to the supplied latent schedule. In the other direction, the core
`recorded_value_error_le` transfers a candidate's latent-time value budget to
recorded-time evaluations. The uniform grids here use unbounded integers and
exact real arithmetic. The separate [binary64 quantization
theorems](../../Silmaril/Numeric/Ieee754/Quantization/Thms.lean) state their own
floating-point hypotheses.
[Quantization bridge](../../Silmaril/Data/TimeSeries/Quantization/Series/Thms.lean)

## Checking the example

```sh
lake build --wfail +Silmaril.Data.TimeSeries.Examples
make check CHECK_TARGETS=+Silmaril.Data.TimeSeries.Examples
```

For a smaller import closure, use `Silmaril.Data.TimeSeries.Thms` for observations
and errors or `Silmaril.Data.TimeSeries.Sampling.Thms` for sampling and additive
value errors. The full entry point includes the manifold and probability layers.
