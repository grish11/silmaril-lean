module

public import Silmaril.LogicGraph.Audit.Defs
public import Silmaril.Logic.Egglog.Core.Egg.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Source.Script.Thms
public import Silmaril.Calculi.LambdaCube.Hets.Examples
public import Silmaril.Logic.Metamath.Peano.Axioms
public import Silmaril.Logic.Metamath.Peano.Interpretation
public import Silmaril.Logic.Metamath.Peano.ZFC
public import Silmaril.Logic.Metamath.SecondOrder.Systems
public import Silmaril.Logic.SetTheory.Inductive.ZF
public import Silmaril.Logic.SetTheory.Inductive.ZFC
public import Silmaril.Logic.SetTheory.Inductive.ZFCInference
public import Silmaril.Wasm.Institution.Api.Graphs.Defs

/-!
# Logic graph: the curated catalogue, entry by entry

`silmaril/logic-graph/catalogue.toml` records, for each of the 137 logics and 158 maps of the
curated catalogue the logic-graph port started from, what it is in this repository: a registered
record, represented by registered records (an instance of a registered family, or the source of
registered comorphisms), not institution-typed (a logical system, proof calculus, translation of
proofs, family of institutions or theorem), or prospective (no Lean declaration). Lean checks
(`logic_catalogue`, `Silmaril.Project.Registry.Institution.Defs`) that every evidence declaration
exists, which is why this module imports the modules that declare them, and that every record named
is registered. The explorer shows the entries on its Coverage page.
-/

silmaril load "silmaril/logic-graph/catalogue.toml"
