module

public import Silmaril.Logic.Institution.Theory
public import Silmaril.Logic.Institution.Hets.DevGraph

@[expose] public section
namespace Silmaril.Logic.Institution.Hets.PresentationGraph
open CategoryTheory Silmaril.Logic.Institution
universe u v w m n

/-- A shared institution presentation as a single-node Hets development graph. -/
def ofPresentation {Sign : Type u} [Category.{v} Sign]
    (I : Sign ⥤ Room.{w,m,n}) (P : Presentation I) : DevGraph I where
  Node := Unit
  sig _ := P.sig
  axioms _ := P.axioms
  globalDef _ _ := ∅
  localDef _ _ := ∅
  hidingDef _ _ := ∅
  wf := ⟨fun node => Acc.intro node (by simp)⟩

end Silmaril.Logic.Institution.Hets.PresentationGraph
