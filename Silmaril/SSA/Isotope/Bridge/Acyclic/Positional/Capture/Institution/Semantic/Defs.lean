module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Thms

/-! # Semantic quotient for the captured ranked comparison -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst)
open Silmaril.SSA.LambdaRTL.Quotient

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

noncomputable abbrev rankedSemanticInstitution : Inst.{1, 0, 0, 0, 1} :=
  Inst.quot (rankedInstitution J)

noncomputable abbrev grammarSemanticInstitution : Inst.{1, 0, 0, 0, 1} :=
  Inst.quot (grammarInstitution J)

end Silmaril.Isotope.Institution.Acyclic.Captured
