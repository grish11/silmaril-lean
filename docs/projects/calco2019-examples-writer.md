# The singleton writer extension in CALCO 2019

Example 20(4) of [Levy and Goncharov, CALCO 2019, article 13][paper], p. 13:10,
extends the ordinary writer `A* × X` by a left action on a singleton. In
[SingletonWriter][writer], `Model` is Mathlib's writer transformer over
partiality with the free monoid on the alphabet. The classical equivalence
`observe` identifies its carrier with `(List A × X) ⊕ PUnit`.

`observe_pure` checks the empty output word on pure return. `observe_bind`
checks concatenation on success and the singleton result if either observation
diverges. `elgot_isElgot` reuses the lawful Elgot writer transformer and the
CALCO type bridge. The instance supports arbitrary loop bodies, including the
ones guarded by a nonempty word.

[WriterAction][action] gives the lawful writer monad for any left action
and its nonempty-word guard. `ordinaryEquiv` recovers the ordinary writer
from the empty action carrier. `ordinary_not_iterative` identifies its
guarded one-letter obstruction. `stream_guarded_iterative` checks unique
guarded solutions for the stream action. `streams_final` checks the
head-and-tail final coalgebra characterization of infinite streams.

The phrase “an inhabited left module” alone does not imply guarded
iterativity. `inhabited_action_counterexample` uses nonempty finite words
with the prepend action. The carrier is inhabited when the alphabet has
a letter, and prepending that letter strictly increases the length.
The singleton and stream choices in the paper satisfy the claimed
remedy by their checked results above. For the separating equation in
Example 20(5), `greatest_letter_trace` checks the exact canonical solution.

For ordinary equivariant maps of left actions, `singleton_action_terminal`
gives the singleton's terminal property, and `no_singleton_to_words`
rejects initiality among inhabited actions when there is a letter.
`no_singleton_to_streams` excludes terminality of the stream action for
two distinct letters. The stream finality checked above is for head-and-tail
coalgebras.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.SingletonWriter \
  +Silmaril.Papers.Calco2019.Examples.WriterActions
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[writer]: ../../Silmaril/Semantics/Calco2019/Examples/SingletonWriter/Thms.lean
[action]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/WriterAction/Thms.lean
