# Checked Peggy loop equations in native λSSA

`peggyToNative` is an institution comorphism on the marked fixed-sort
signature category from [#4047](https://github.com/hiloopai/silmaril-lean/pull/4047).
It translates each checked loop equation to the two typed Isotope regions
emitted by [#4180](https://github.com/hiloopai/silmaril-lean/pull/4180).
The common carried list gives the entry and sole exit packet types in order.
[Definitions and bundled arrows](../../Silmaril/SSA/Peggy/Bridge/Theta/LambdaSSA/Thms.lean)

The factorization is `peggyToThetaImage` followed by `thetaImageToNative`.
The intermediate sentence retains the actual numbered θ equation and its
two native regions, admitted by a common certificate on each side. Its
satisfaction is the existing θ equation satisfaction in the induced total
model. The native endpoints retain the particular scheduled lowering,
which the existing θ sentence interface does not carry. Forgetting those
endpoints recovers the existing `peggyToTheta` comorphism on the
underlying Peggy equation. `thetaImage_agrees` proves equality of the
two bundled composites. [Paired compiler image](../../Silmaril/SSA/Peggy/Bridge/Theta/LambdaSSA/Defs.lean)

The existing Isotope observational institution uses fixed opcode alphabets
and also observes faults and divergence. The restricted target here
admits typed native regions at the ordered packet boundary. In a marked
pure total model, its equations compare `Region.Eval` at exit zero on all
typed input and output packets, with unit ambient state. A nonreturn
contributes no tuple to this relation. For compiled endpoints, the
finite-return theorem matches this relation to the fully defined Figure 11
first-exit tuple with its shared pass and defined prefixes. The original θ
satisfaction clause is used through #4047's theorem for total θ bodies.
The λSSA result covers successful finite returns, with partiality, traps,
and divergence outside its scope.

The signature functor is identity on marked signatures. Relabeling uses
Isotope's `Region.mapInstr`, fixes the structural Boolean test, and
preserves each typed opcode profile. `lower_map` proves equality of the
whole emitted syntax, including binders, packet order, CFG entry, and
backedge and exit labels. The model comparison is identity on the common
total primitive presentation. Along a signature arrow the model reduct
precomposes the primitive functions and retains the carriers and the
marked Boolean negation law. The guard test keeps its false-exit and
true-feedback polarity. `returns_map` uses preservation and reflection
of native evaluation even for an opcode map that identifies two names.
[Native relabeling](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaSSA/Relabel/Thms.lean) ·
[Finite evaluation under relabeling](../../Silmaril/SSA/Isotope/LambdaSSA/InstructionMap/Thms.lean)

The three-slot regression identifies `add` with `addAlt`. The native
relabeling changes the return from `(0, 11, 12)` to `(0, 12, 14)`. The
same changed tuple is observed by the original code in the reduct. The
equation is false before relabeling and true after the two opcodes are
identified. [Regression](../../tests/ssa/PEGStructuredTheta.lean)

## Checks

```sh
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
```
