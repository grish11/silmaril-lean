module

public import Silmaril.Logic.Separation.Parameterized.Institution.Defs
public import Silmaril.Wasm.Logic.Separation.Parameterized.Lists.Examples

@[expose] public section
namespace Silmaril.Logic.Separation.Parameterized

/-- info: 'Silmaril.Logic.Separation.Parameterized.lfpSet_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lfpSet_unfold

/-- info: 'Silmaril.Logic.Separation.Parameterized.lfpSet_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lfpSet_induction

/-- info: 'Silmaril.Logic.Separation.Parameterized.Pattern.denote_lfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Pattern.denote_lfp

/-- info: 'Silmaril.Logic.Separation.Parameterized.Pattern.denote_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Pattern.denote_map

/-- info: 'Silmaril.Logic.Separation.Parameterized.Sentence.satisfaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sentence.satisfaction

/-- info: 'Silmaril.Logic.Separation.Parameterized.reductFunctor_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reductFunctor_id

/-- info: 'Silmaril.Logic.Separation.Parameterized.reductFunctor_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reductFunctor_comp

/-- info: 'Silmaril.Logic.Separation.Parameterized.institution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms institution

/-- info: 'Silmaril.Logic.Separation.Parameterized.Lists.list_iff_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Lists.list_iff_linked

/-- info: 'Silmaril.Logic.Separation.Parameterized.Lists.Examples.source_two_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Lists.Examples.source_two_nodes

/-- info: 'Silmaril.Logic.Separation.Parameterized.Lists.Examples.source_null_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Lists.Examples.source_null_empty

/-- info: 'Silmaril.Logic.Separation.Parameterized.Lists.Examples.source_nonnull_empty_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Lists.Examples.source_nonnull_empty_false

end Silmaril.Logic.Separation.Parameterized
