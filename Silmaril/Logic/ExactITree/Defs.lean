module

public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Silmaril.Semantics.ExactITree.Thms

/-! The institution of exact weak-tree lowering, with discrete relational kernels. -/

@[expose] public section

namespace Silmaril.Elgot.ITree.Exact

universe u v

/-- The Goguen–Burstall institution for a fixed sequential observation profile. -/
def institution (P : Profile.{v}) : Silmaril.Inst.Plain Signature.{u} where
  Sen := Sentence P
  map f φ := φ.lower f
  map_id _ := Sentence.lower_id
  map_comp f g := Sentence.lower_comp f g
  Mod := Kernel P
  reduct := Kernel.reduct
  reduct_id _ := Kernel.reduct_id
  reduct_comp := Kernel.reduct_comp
  Sat := Satisfies
  sat_map := satisfies_lower

end Silmaril.Elgot.ITree.Exact
