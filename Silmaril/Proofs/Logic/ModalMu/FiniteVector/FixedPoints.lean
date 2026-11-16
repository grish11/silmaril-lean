module

public import Silmaril.Logic.ModalMu.FiniteVector.Defs

@[expose] public section
namespace Silmaril.Logic.ModalMu.FiniteVector

def orderMap {α β : Type} [Preorder α] [Preorder β] (e : α ≃o β) : α →o β :=
  ⟨e, e.monotone⟩

/-- Fixed points commute with an actual order isomorphism, for either kind. -/
theorem fixed_conjugate {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (e : α ≃o β) (f : α →o α) (greatest : Bool) :
    e (Vector.fixed greatest f) = Vector.fixed greatest
      ((orderMap e).comp (f.comp (orderMap e.symm))) := by
  let g := (orderMap e).comp (f.comp (orderMap e.symm))
  cases greatest
  · change e f.lfp = g.lfp
    have h : f (e.symm g.lfp) = e.symm g.lfp := by
      apply e.injective
      calc
        e (f (e.symm g.lfp)) = g g.lfp := rfl
        _ = g.lfp := g.map_lfp
        _ = e (e.symm g.lfp) := (e.apply_symm_apply _).symm
    apply le_antisymm
    · exact (e.monotone (f.lfp_le h.le)).trans_eq (e.apply_symm_apply _)
    · apply g.lfp_le
      change e (f (e.symm (e f.lfp))) ≤ e f.lfp
      rw [e.symm_apply_apply, f.map_lfp]
  · change e f.gfp = g.gfp
    have h : f (e.symm g.gfp) = e.symm g.gfp := by
      apply e.injective
      calc
        e (f (e.symm g.gfp)) = g g.gfp := rfl
        _ = g.gfp := g.map_gfp
        _ = e (e.symm g.gfp) := (e.apply_symm_apply _).symm
    apply le_antisymm
    · apply g.le_gfp
      change e f.gfp ≤ e (f (e.symm (e f.gfp)))
      rw [e.symm_apply_apply, f.map_gfp]
    · exact (e.apply_symm_apply _).symm.trans_le (e.monotone (f.le_gfp h.ge))

/-- Split a finite valuation into its first coordinate and remaining coordinates. -/
def splitEnv (W : Type) (k : Nat) : Env W (k+1) ≃o (Set W × Env W k) where
  toFun X := (X 0, fun i => X i.succ)
  invFun P := Fin.cases P.1 P.2
  left_inv X := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv P := by cases P; rfl
  map_rel_iff' := by
    intro X Y
    constructor
    · intro h i
      exact Fin.cases h.1 h.2 i
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

end Silmaril.Logic.ModalMu.FiniteVector
