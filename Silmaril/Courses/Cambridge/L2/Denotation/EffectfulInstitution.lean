module

public import Silmaril.Courses.Cambridge.L2.Denotation.EffectfulAdequacy
public import Silmaril.Courses.Cambridge.L2.OperationalInstitution
public import Silmaril.Logic.Fragments.Institution.Thms

/-! # Institutional comparison for effectful ground observations -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.EffectfulDenotation

open CategoryTheory Silmaril.Logic.Fragments Silmaril.Semantics.Operational
open PureDenotation (Ground)

/-- An admitted source packages the exact typing, ground observation and
store-coverage hypotheses of finite adequacy. -/
structure ObservationSource where
  locations : L1.TypeEnv
  expression : Expr
  type : Ty
  term : Term locations [] expression type
  ground : Ground type
  store : Store
  covers : Covers locations store

def ObservationSource.config (source : ObservationSource) : Config :=
  ⟨source.expression, source.store⟩

/-- An atomic sentence proposes a returned value and final store. -/
def signature : AtomicSignature := ⟨ObservationSource × Config⟩

def model : AtomicModel signature :=
  fun (source, target) => target ∈ source.term.observe source.ground source.store

theorem sat_iff (source : ObservationSource) (target : Config) :
    (atomicInstitution.obj signature).Sat (Discrete.mk model) (source, target) ↔
      OperationalInstitution.semantics.May source.config (.returned target) :=
  (source.term.adequate source.ground source.covers target).trans
    (OperationalInstitution.may_return_iff _ _).symm

end Silmaril.Courses.Cambridge.L2.EffectfulDenotation
