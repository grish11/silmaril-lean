# Restricted Peggy to numbered RVSDG θ comorphism

`peggyToTheta` is an institution comorphism over the category of
fixed-sort Peggy signatures with a marked unary Boolean negation
primitive. A signature arrow is a Peggy opcode map preserving the marked
symbol and each ordered profile. `thetaSignature` sends these signatures
and arrows to the existing RVSDG signature category. Primitive θ opcodes
follow that map, and the synthetic branch-tag opcode stays fixed.
[Signature and sentence definitions](../../Silmaril/SSA/Peggy/Bridge/Theta/Defs.lean)

The source equations have the same carried boundary on both sides. Each
side contains a numbered PEG and its scheduled θ image. Admission
requires an ordered single-loop certificate that compiles to that image.
Keeping the schedule image in the sentence makes the translation
deterministic even when several valid schedules exist. Opcode relabelling
maps the actual PEG table and its schedule, and the resulting compilation
is exactly relabelling the numbered θ body with the canonical IR map.
[Compiler naturality](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Relabel/Thms.lean) ·
[Ordered bridge](peg-theta-tuple-observation.md)

PEG delay is structural. A θ feedback edge requests the previous
iteration, and the initial arm supplies iteration zero. Relabelling
changes neither the loop identity nor the feedback, initializer, pass
or eval references. The exit row uses the marked primitive. Models give
it Boolean negation, which is preserved by contravariant opcode reduct.
The RVSDG continuation arm is selected by the unnegated guard. The
translation keeps the shared first-exit and prefix semantics of the
checked ordered bridge.

The target is the existing numbered θ institution pulled back along
`thetaSignature`, with canonical satisfaction and a restricted model
family. A model is presented by a pure total PEG interpretation with the
marked negation law. It induces an actual RVSDG model with fixed
structural branch tags and the PEG carriers. `theta_reduct` identifies
reduct in this family with the canonical RVSDG opcode reduct.
`restrictThetaModels` bundles the comparison with the canonical target.
The comorphism translates equations with `Equation.translate` and pulls
back a target model to its presenting PEG model. The sentence and model
maps are natural along every marked opcode map.
[Bundled institutions and comorphism](../../Silmaril/SSA/Peggy/Bridge/Theta/Thms.lean)

Source satisfaction compares the relation of fully defined ordered
Figure 11 observations at every input and ambient index. A nonreturn
has no complete tuple in that relation. On the target side the original
θ equation compares both finite returns and divergence. The existing
partial-value adequacy theorem proves that, for total deterministic θ
bodies, divergence is equivalent to absence of a finite return. This
recovers the canonical target's divergence clause from agreement on
finite returns. Equality of partial PEG tuples, partial primitives,
effects and nested loops are outside the source institution here.
[Satisfaction proof](../../Silmaril/Proofs/SSA/Peggy/Bridge/Theta/Satisfaction.lean)

## Checks

```sh
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
for module in \
  Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Defs \
  Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Relabel.Compiler \
  Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Thms \
  Silmaril.SSA.Peggy.Bridge.Theta.Defs \
  Silmaril.Proofs.SSA.Peggy.Bridge.Theta.Naturality \
  Silmaril.Proofs.SSA.Peggy.Bridge.Theta.Satisfaction \
  Silmaril.SSA.Peggy.Bridge.Theta.Thms tests.ssa.PEGStructuredTheta; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The three-slot numbered fixture uses a nonidentity opcode map fixing the
marked negation. The new primitive changes the first update from
`(1, 1, 11)` to `(1, 1, 12)`. The fixture instantiates sentence
naturality, the bundled satisfaction condition, and the canonical
model restriction.
[Regression](../../tests/ssa/PEGStructuredTheta.lean)
