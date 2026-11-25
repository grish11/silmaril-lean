# INSTANCE replay for DataElab

The #3042 interface can replay the tested first-order instances with their
original host expressions. The probe found no checker defect in named
argument order, nested contexts, repeated instances, or endpoint selection.
The later [nested LOCAL level regression](tla-local-instance-cap.md) covers a separate declaration-level case and records its fix on #3042.

[Checked scratch probe](tla-instance-replay-probe.lean) · [Pinned #3042 API](https://github.com/hiloopai/silmaril-lean/blob/ff79ead608d9d1da327261368d9996a6ddd9193f/docs/projects/tla-module-instantiation.md)

## Entry and certificate

- If the entry takes raw `Registry`, call `Instances.check registry root externalLevels`
  once. Consume the returned `CheckedInstances` as a pair. Its private constructor
  prevents replacing the levels field through ordinary Lean record update.
- If the entry already takes a `CheckedRegistry`, its names, arities, and
  instance plans have been resolved for its original syntax profile. Run
  `Levels.check` on that exact registry with the caller's external level
  signatures, then pass both results inside the lowerer's private checked
  context. The external level signatures remain caller attestations.
  DataElab's primitive interpretation and its value laws remain separate. A graph resolved under the core profile has no instance plans
  for rejected instance syntax.
- Treat separately supplied `CheckedLevels` as unpaired until there is a
  same-graph check. A `BindingId` is scoped to its graph. The probe constructs
  two graphs with the same ID and path for `Out`, one state-level and one
  action-level. An ID lookup alone would let an adapter gate the wrong
  expression with the other graph's certificate.
- Gate a selected closed nullary definition or generated member using
  `operatorAt id`. Check the generated member summary when there is one.
  `expressionAt` at the home path gives the original module annotation,
  which can differ after a substitution. Keep DataElab's own syntax gate,
  primitive admission, and Boolean result policy.

[Level API and signature contract](https://github.com/hiloopai/silmaril-lean/blob/05aa612fe1ee7dd74a5464041cb21546d44477e2/docs/projects/tla-expression-levels.md)

## Replay sequence

1. Resolve a call from the reference at the whole expression's `Site`.
   For a qualified call, use `qualifiedCall` and `qualifiedArguments`
   to keep the head and selector argument paths and obtain their ordered
   actuals. Store each actual as a suspended expression in its original
   caller context. The checked argument group counts are in
   `InstanceMember.argumentCounts`.
2. When `memberAt id` returns a plan, split off `plan.parameters.length`
   actuals for the namespace and bind them by ID. Capture the host frame
   with those bindings **before** installing any replacements. Build the
   target frame by mapping each target ID to a suspension. An explicit
   replacement uses its stored host `Site` and expression. An omitted WITH
   entry reads the stored host ID in the captured frame. This matters even
   when the host and target inherited exactly the same ID.
3. Enter the home binding under the target frame and pass the remaining
   actuals. If that home is another generated member, repeat the same split
   and capture step under the enclosing replay frame. Ordinary home bodies
   and their LOCAL callees use their original source sites and references.
   Anonymous instances with an empty substitution environment may already
   point to the original binding. The same home ID can be entered with
   different actuals or substitutions, so a body cache needs the captured
   environment as part of its key.
4. Keep flexible reads relative to the current endpoint. Prime shifts the
   entire lowered operand to the target endpoint and preserves rigid
   assignments. A home reference to a replaced declaration then forces
   the host expression at that endpoint. Namespace and member actuals are
   also endpoint-relative. Avoid freezing actuals at the entry endpoint.
   Syntactic checking can inspect every actual even when an unused
   argument's denotation is never forced.

[Lamport, *Specifying Systems*, §17.8](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=352)

## DataElab seams

- **Applications and selection.** Extend the existing
  `lowerApplication` argument traversal to use the segment paths.
  Dispatch generated members before `applyGlobal` tries `sourceBody`.
  The same branch is needed at `lowerDefinition` when a caller selects a
  generated nullary member directly. Preserve the home and host sites for
  diagnostics.
- **Binding frames.** Carry the active instance frame through
  `applyBinding`, `applyGlobal` and home-body expansion, including private
  global helpers. Keep the lexical bindings used for actuals, LET closures
  and witnesses separate from the module substitutions. Resolve
  replacement reads before ordinary variable or constant reads and keep
  primitive dispatch by exact declaration identity. Already expanded
  terms can serve as suspensions if their flexible reads remain
  endpoint-relative and their witness slots stay scoped.
- **Endpoint semantics.** Lower checked prime to a term that switches the
  endpoint for its operand. Apply this to the expanded operand, including
  any referenced replacement and actual. The caller's two-endpoint
  interpretation supplies flexible values; tagged operators consume the
  resulting operands. Replay itself needs no global set extensionality
  or value-model change. The probe covers Boolean values and the endpoint
  change, while the owner's tagged and endpoint layer supplies the real
  denotation.
- **Boundaries.** Keep theorem substitution and operator-valued
  substitutions outside this entry. A proof-free host statement has a
  level annotation and no theorem binding. #3030 has single-state support
  for some operator arguments, but the first-order whole-registry
  certificate can reject higher-order forms before lowering. The probe
  exercises both rejection paths and excludes ENABLED, fairness, temporal
  denotation, and quantified values.

[Pinned DataElab lowering at #3030](https://github.com/hiloopai/silmaril-lean/blob/6beb478f57b4cc935260a5bcd893b935296060db/Silmaril/Logic/Temporal/TLA/DataElab/Defs.lean) ·
[Tagged value operations](https://github.com/hiloopai/silmaril-lean/blob/38d2485cab1191214692a97c6ad00e293b5d3cc0/docs/projects/tla-tagged-values.md)

## Verification

```sh
lake build --wfail \
  +Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs \
  +Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
lake env lean -DautoImplicit=false -DwarningAsError=true \
  --run /work/out/tla-instance-replay-probe.lean
```

The probe compared five replayed definitions with direct Boolean formulas
over all 64 source/target pairs. It covered repeated named instances, an
indirect home call, a WITH expression calling an earlier instance, and an
action-level RHS from a constant module. Twelve more checks exercised implicit
substitution where both sides had the same inherited binding ID, including
direct and indirect nested replay through a changing outer replacement. Three
negative calls independently exceeded the state cap in the outer namespace,
inner namespace, and home member slots. The pinned SANY frontend also
accepted the positive nested fixture with all five selected definitions at
action level. These are scoped executable checks.
