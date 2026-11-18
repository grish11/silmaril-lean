module

public import Silmaril.Machine.Translation.Defs
public import Silmaril.Machine.CBackend.Behaviour.Refinement.Defs

/-! # Soundness of a translation relation under chosen semantics -/

@[expose] public section

namespace Silmaril.Machine.Translation

inductive Direction where
  | targetRefinesSource
  | sourceRefinesTarget

/-- Each related artifact pair must refine in the indicated direction.
Entry and observation arguments are given in source/target order. The side
being refined supplies the safety premise to `Behaviour.Refines`. This
predicate does not itself require either side to have a behaviour. -/
def Sound {Src Tgt SrcState TgtState SrcRet TgtRet SrcTrap TgtTrap SrcFault TgtFault : Type*}
    (rel : Relation Src Tgt) (direction : Direction) (mode : Behaviour.Mode)
    (source : Src → Behaviour.Semantics SrcState SrcRet SrcTrap SrcFault)
    (target : Tgt → Behaviour.Semantics TgtState TgtRet TgtTrap TgtFault)
    (initial : Src → Tgt → SrcState → TgtState → Prop)
    (observation : Src → Tgt → SrcState → TgtState →
      Behaviour.Obs SrcRet TgtRet SrcTrap TgtTrap SrcFault TgtFault) : Prop :=
  ∀ src tgt, rel src tgt → match direction with
  | .targetRefinesSource => Behaviour.Refines mode (target tgt) (source src)
      (fun tgtState srcState => initial src tgt srcState tgtState)
      (fun tgtState srcState => (observation src tgt srcState tgtState).flip)
  | .sourceRefinesTarget => Behaviour.Refines mode (source src) (target tgt)
      (initial src tgt) (observation src tgt)

end Silmaril.Machine.Translation
