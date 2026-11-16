module

public import Silmaril.Logic.ModalMu.Vector.Defs

@[expose] public section
namespace Silmaril.Logic.ModalMu.Vector

/-- Genuine product-lattice Bekič decomposition for least fixed points. -/
theorem bekic_lfp {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (f : (α × β) →o (α × β)) :
    f.lfp = ((reduced false f).lfp, secondSolutions false f (reduced false f).lfp) := by
  let a := (reduced false f).lfp
  let b := secondSolutions false f a
  have hb : (f (a, b)).2 = b := (secondAt f a).map_lfp
  have ha : (f (a, b)).1 = a := (reduced false f).map_lfp
  have upper : f.lfp ≤ (a, b) := f.lfp_le ⟨ha.le, hb.le⟩
  have hbeta : secondSolutions false f f.lfp.1 ≤ f.lfp.2 := by
    apply (secondAt f f.lfp.1).lfp_le
    exact (congrArg Prod.snd f.map_lfp).le
  have halpha : a ≤ f.lfp.1 := by
    apply (reduced false f).lfp_le
    have hp : (f.lfp.1, secondSolutions false f f.lfp.1) ≤ f.lfp := ⟨le_rfl, hbeta⟩
    exact ((f.mono hp).1).trans (congrArg Prod.fst f.map_lfp).le
  exact le_antisymm upper ⟨halpha, ((secondSolutions false f).mono halpha).trans hbeta⟩

/-- Genuine product-lattice Bekič decomposition for greatest fixed points. -/
theorem bekic_gfp {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (f : (α × β) →o (α × β)) :
    f.gfp = ((reduced true f).gfp, secondSolutions true f (reduced true f).gfp) := by
  let a := (reduced true f).gfp
  let b := secondSolutions true f a
  have hb : (f (a, b)).2 = b := (secondAt f a).map_gfp
  have ha : (f (a, b)).1 = a := (reduced true f).map_gfp
  have lower : (a, b) ≤ f.gfp := f.le_gfp ⟨ha.ge, hb.ge⟩
  have hbeta : f.gfp.2 ≤ secondSolutions true f f.gfp.1 := by
    apply (secondAt f f.gfp.1).le_gfp
    exact (congrArg Prod.snd f.map_gfp).ge
  have halpha : f.gfp.1 ≤ a := by
    apply (reduced true f).le_gfp
    have hp : f.gfp ≤ (f.gfp.1, secondSolutions true f f.gfp.1) := ⟨le_rfl, hbeta⟩
    exact (congrArg Prod.fst f.map_gfp).ge.trans ((f.mono hp).1)
  have upper : f.gfp ≤ (a, b) := ⟨halpha, hbeta.trans ((secondSolutions true f).mono halpha)⟩
  exact le_antisymm upper lower

theorem bekic {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (greatest : Bool) (f : (α × β) →o (α × β)) :
    fixed greatest f = (fixed greatest (reduced greatest f),
      secondSolutions greatest f (fixed greatest (reduced greatest f))) := by
  cases greatest
  · exact bekic_lfp f
  · exact bekic_gfp f

end Silmaril.Logic.ModalMu.Vector
