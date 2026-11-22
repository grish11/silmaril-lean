# Operational program comparisons

`HasOpSem Program State Obs` is the only entry-bearing model. Its `initial`
relation describes entry in context, and its `WithUB` describes actual states.
It does not require total or unique entry. Use `Outcome (Except Error Result)`
when a language exposes both values and errors: `.returned (.ok value)`,
`.returned (.error err)`, and `.trap` are three different observations. A
missing entry is `NoEntry`; `WithUB.Stuck` is an unclassified, non-UB state
with neither a move nor an observation. Neither implies an infinite path.
Open host requests need their own observable interface rather than being
interpreted as UB or an error by default.

[`Program.Thms`](../../Silmaril/Semantics/Operational/Program/Thms.lean) adds:

| Operation | What it means |
| --- | --- |
| `precompose` / `restrictPrograms` | Change the input syntax (e.g. erase a proof-carrying term) or select admitted programs. No change to execution policy. |
| `restrictStates` | Select a subtype of states; can drop crossing steps. Backwards readback needs closure; use the existing `WithUB.restrict_readback`. |
| `.semantics.toOpSem` | Forget UB, leaving all ordinary steps and observations, even from unsafe starts. |
| `safeFragment` | Select states that cannot reach UB. This subtype is closed and its finite outcomes are exactly those from the original safe entries. |
| `mapObservations` | Interpret returned values and explicit errors in a common alphabet; keeps traps and UB. Compatible with `precompose` and preserves `Refines` under a shared map. |
| `SameFinite` | Equality of finite observation sets, not trace or step equality. |
| `UBRefines` / `Refines` | No new reachable UB, and (for `Refines`) unconditional inclusion of finite outcomes. |
| `Equivalent` | Mutual `Refines`, exactly `SameFinite` plus equivalent reachability of UB. |

For erasure between machines, pass their state relation to the existing
`OpSim` and match **every** implementation entry with a specification entry.
`refines_of_sim` transfers finite outcomes and possible UB forward. A reverse
simulation needs its own step, observation, UB, and initialization evidence.
Stuttering simulations need not reflect divergence; finite equivalence need
not reflect missing entry or stuckness. Observer projection is a proved
compatibility rule, not contextual congruence under linking. `OpSim.id` and
`OpSim.trans` already provide identity and composition with relational state
composition; no new category or institution is implied here.

Primitive meet/join use [`WithUB.Included`](../../Silmaril/Semantics/Operational/Policy/Thms.lean).
Mixed policy approximation and guarded safe refinement have distinct meanings;
see [determinism and fuel](opsem-determinism.md). `DetFrom` is primitive
uniqueness on reachable states, and `NonTrapDetAt` is uniqueness of non-trap
payloads (including explicitly observed errors); possible traps do not violate
the latter. Use `Oracle.run_sound` and the finite completeness theorem with its
reachability, terminal, determinism and coverage premises. Fuel exhaustion or
an unknown choice is not evidence of UB, stuckness or divergence.

Run `make check CHECK_TARGETS=+Silmaril.Semantics.Operational.Program.Thms`
for the regression and axiom audit.
