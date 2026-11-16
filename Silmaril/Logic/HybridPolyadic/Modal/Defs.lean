module

public import Silmaril.Logic.HybridPolyadic.Thms
public import Silmaril.Logic.Modal.Thms

/-! # Actual normal-K to hybrid/polyadic institution comorphism

The source has all ordinary bounded morphisms. The target uses the stricter
injective bounded maps. The reduct forgets injectivity; object expansion does
not assert that every source arrow has an expansion.
-/

@[expose] public section
namespace Silmaril.Logic.HybridPolyadic
open CategoryTheory Silmaril.Logic.Institution

/-- Ordinary K adds one unary action and no nominals. -/
def modalSignatures : Modal.Signature ⥤ Signature where
  obj S := ⟨S.Atom, Empty, fun k => PLift (k = 1)⟩
  map f := ⟨f, id, fun _ => id⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def modalAction {S : Modal.Signature} : (modalSignatures.obj S).Action 1 := ⟨rfl⟩

def Formula.unaryDia {S : Signature} {n : ℕ} (a : S.Action 1) (p : Formula S n) :
    Formula S n := .dia a (fun _ => p)

def Formula.unaryBox {S : Signature} {n : ℕ} (a : S.Action 1) (p : Formula S n) :
    Formula S n := (p.neg.unaryDia a).neg

/-- Forget names, other arities and injectivity, retaining the actual unary relation. -/
def modalReduct (S : Modal.Signature) : Model (modalSignatures.obj S) ⥤ Modal.Model S where
  obj M := ⟨M.World, fun w v => M.relation 1 modalAction w (fun _ => v), M.valuation, M.point⟩
  map h :=
    { map := h.map
      point := h.point
      atoms := h.atoms
      forth := fun w v hv => h.forth 1 modalAction w (fun _ => v) hv
      back := by
        intro w v hv
        obtain ⟨us, hu, heq⟩ := h.back 1 modalAction w (fun _ => v) hv
        refine ⟨us 0, ?_, congrFun heq 0⟩
        have hus : (fun _ : Fin 1 => us 0) = us := by
          funext i
          rw [Fin.eq_zero i]
        change Silmaril.Logic.HybridPolyadic.Model.relation _ 1 _ w _
        rw [hus]
        exact hu }
  map_id _ := rfl
  map_comp _ _ := rfl

def encodeModal {S : Modal.Signature} {n : ℕ} : Modal.Formula S → Formula (modalSignatures.obj S) n
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .imp (encodeModal p) (encodeModal q)
  | .box p => (encodeModal p).unaryBox modalAction

/-- Every K model expands on exactly the same arbitrary carrier and frame. -/
def expandModal {S : Modal.Signature} (M : Modal.Model S) : Model (modalSignatures.obj S) where
  World := M.World
  relation k a w vs := M.accessible w (vs ⟨0, by have hk := a.down; omega⟩)
  valuation := M.valuation
  name := Empty.elim
  point := M.point

end Silmaril.Logic.HybridPolyadic
