# Figure 18 completion for one parent/child while

`Structured.Token.Nested.Form` describes an outer SIMPLE while that,
on every continuing step, projects a typed child entry from its old store,
runs one unconditional child while, then commits from the child exit
store. The capture can duplicate outer slots or carry them through the
child for the commit. The child body and commit are loop-free and can use
the conditional completion compiler. [Compiler](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Defs.lean)

The emitted PEG uses the structured compiler's parent relation and demand
rank. Each loop retains an ordinary Figure 11 first pass and a carried
completion θ. The child's θ takes the current outer token at child
iteration zero. Its eval samples that child token using the child pass,
at the current outer coordinate. The commit uses the child exit token as
its incoming token. The next outer token therefore requires this child's
exit in addition to the complete commit. At an outer zero trip, the
outer marker samples the seed and requires no child exit. This uses the
same pass-and-eval encoding as the single-loop slice of Figure 18.
[Figure 18 and §6.4](https://arxiv.org/pdf/1012.1802v3#page=39)

With the Boolean negation law, an original successful SIMPLE return
defines the ordered data and completion roots. Conversely, a defined
outer completion root reconstructs an original successful SIMPLE run
with the same data value. The stronger trace theorem also identifies the
outer pass count and exhibits a defined child pass and marker at each
continuing outer coordinate. The proof uses the scoped single-loop
correspondence for every child activation and the existing loop-free
interpreter correspondence for the commit. It requires neither global
primitive totality nor a separate termination premise.
[Theorems](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Thms.lean)

The regressions reuse the countdown source with child trip counts two
then one and accumulated result `4`. A second graph retains a defined
data result despite a discarded strict operation failing in the child.
Its completion root is bottom when the parent continues and defined
when the parent takes zero trips with the same child input.
[Regressions](../../tests/ssa/PEGSimple.lean)

The fragment has one outer loop and one child, with projection-only
captures. It covers successful completion and uses bottom as the common
absence of completion for failures and divergence. Arbitrary nesting
and general effect-token semantics remain outside the result. The
[conditional-child extension](peggy-figure18-conditional-child.md)
handles one child in a selected outer arm.
