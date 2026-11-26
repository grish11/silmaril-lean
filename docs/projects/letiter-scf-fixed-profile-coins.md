# A fixed-profile LetIter and scalar SCF institution isomorphism

`Silmaril.MLIR.SCF.LetIter.FixedProfile.scalarNativeIso P` is an isomorphism
in `CoIns` for the one-loop scalar fragment. A profile `P` fixes four
ordered lists of scalar widths for ambient inputs, before state, condition
payload, and results. The profiles can differ from each other. Each object
uses the same profile on both sides of the comparison.

## The two presentations

The SCF presentation uses a typed initializer, before region, after region
and parent. Its observations come from the independent `SCF.While` evaluator.
The native presentation admits closed positional LetIter syntax by a
phase-indexed grammar. The condition reads the current before state. A
false result exits with the condition payload. The yield and parent read the
payload; the before state's local slot is unavailable to either. The
grammar admits an identity `let₁ t (.bv 0)` at every phase. Exact typing is
checked by `Grammar.hasType`. The decoder reads the initializer and three
typed regions from a grammar derivation, ignoring identity wires.

The `Examples` module checks a native program with identity wires around the
whole program and around the condition. Its syntax differs from every
direct scalar encoding, and it represents the same quotient class as the
direct encoding of the decoded program. The example also uses a
profile-preserving opcode map and exercises one finite exit and a divergent
backedge under different renamings.

The native presentation interprets each of the four scalar blocks as one
primitive call at its typed interface. The independent SCF evaluator
executes its typed block bindings. Native LetIter supplies the iteration,
sum elimination, sequencing, and operand wiring. The bridge in
[#3178](https://github.com/hiloopai/silmaril-lean/pull/3178) supplies the
finite-return, divergence, and no-fault lemmas. Identity-wire elimination
uses native observational congruence for all three observations.

## Sign, Sen, Mod and Sat

- **Sign** is the category `Signature` of `Pure.OpSignature` families.
  A morphism maps each opcode to an opcode with the same ordered operand
  widths and result width. `renameCode` acts on typed block bindings.
  `renameCall` acts on the four native call forms, and `Native.rename`
  applies the native term instruction map while preserving admission.
- **Mod** has discrete categories of total deterministic `Pure.Eval`
  evaluators. `reduct` precomposes with the opcode map.
  `modelReduct_id` and `modelReduct_comp` check the functor laws.
- **Sen** has equations and refinements between observational program
  classes. Quotient equality means equality of answer sets at every
  evaluator and typed input. Sen reindexes both programs.
  `renameQ_id` and `renameQ_comp` check identity and composition.
- **Sat** requires equal answer sets for equations and inclusion for
  refinements at every typed input for the selected evaluator. A scalar
  return exists when some fuel budget returns the specified value.
  Scalar divergence means every finite budget returns no value. Native
  return and divergence come from `iterBeh` with the fixed scalar call
  model. `Native.ret_iff` accounts for all native return values and
  `Native.no_fault` rules out a third observable outcome in these models.
  `Presentation.satisfaction` checks change of notation.

`encodeQ` and `decodeQ` commute with signature reindexing. Their
translations are identity on signatures and models, with the shared model
reduct as above. `scalarNativeIso` proves both compositions equal to the
identity comorphism, using the two inverse laws on quotient sentences.
Each side has its own grammar and observation function. The result covers
whole-block calls and exactly one native `iter` with the stated wiring
grammar. General native programs, instruction-by-instruction lowering,
and changes to the four fixed width lists are outside this fragment.
