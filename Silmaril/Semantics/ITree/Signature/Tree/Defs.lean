module

public import Silmaril.Semantics.ITree.Signature.Defs
import Silmaril.Proofs.Semantics.ITree.Signature.Coherence

@[expose] public section

namespace Silmaril.Elgot.ITree.Signature

open CategoryTheory

universe u v w

variable {S T : Signature.{u}} {A : Type v} {B : Type w}

/-- Translate a weak interaction tree by translating every finite observation. -/
def Hom.tree (f : S ⟶ T) (a : A → B) (t : Tree S.Event A) : Tree T.Event B where
  observe n := f.approx a n (t.observe n)
  coherent n := by rw [Proofs.truncate_approx, t.coherent]

end Silmaril.Elgot.ITree.Signature
