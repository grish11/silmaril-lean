module

public import Silmaril.Logic.Matching.FixedPoint.Thms
public import Silmaril.Logic.ModalMu
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)

/-- Atoms are nullary sets; every primitive action is a unary relation. -/
inductive ModalOperation (L : ModalMu.Signature) : (n : Nat) → (Fin n → Unit) → Unit → Type
  | atom (a : L.Atom) : ModalOperation L 0 Fin.elim0 ()
  | action (a : L.Action) : ModalOperation L 1 (fun _ => ()) ()

abbrev modalSignature (L : ModalMu.Signature) : Signature Unit := ⟨ModalOperation L⟩

def modalSignatureMap {L K : ModalMu.Signature} (f : L ⟶ K) : modalSignature L ⟶ modalSignature K where
  operations op := match op with | .atom a => .atom (f.atom a) | .action a => .action (f.action a)

def modalSignatures : ModalMu.Signature ⥤ Signature Unit where
  obj := modalSignature
  map := modalSignatureMap
  map_id _ := by apply Algebraic.ManySorted.Signature.Hom.ext; intro n inputs output op; cases op <;> rfl
  map_comp f g := by apply Algebraic.ManySorted.Signature.Hom.ext; intro n inputs output op; cases op <;> rfl

abbrev modalSets (n : Nat) : Fin n → Unit := fun _ => ()

def encodeModal {L : ModalMu.Signature} : {n : Nat} → ModalMu.Formula L n →
    Pattern (modalSignature L) (modalSets n) (k := 0) Fin.elim0 ()
  | _, .pos a => .app (.atom a) (fun i => i.elim0)
  | _, .neg a => .dualApp (.atom a) (fun i => i.elim0)
  | _, .bot => .base FirstOrder.Pattern.bottom
  | _, .top => .base FirstOrder.Pattern.top
  | _, .var i => .setvar i
  | _, .conj p q => .conj (encodeModal p) (encodeModal q)
  | _, .disj p q => .disj (encodeModal p) (encodeModal q)
  | _, .diamond a p => .app (.action a) ![encodeModal p]
  | _, .box a p => .dualApp (.action a) ![encodeModal p]
  | _, .mu p => .mu (encodeModal p)
  | _, .nu p => .nu (encodeModal p)

/-- Orientation is explicit: result w ∈ action(a)(v) exactly when w →a v. -/
def forgetModal {L : ModalMu.Signature} (M : PointedModel () (modalSignature L)) : ModalMu.Model L :=
  ⟨M.base.carrier (), fun a w v => w ∈ M.base.operation (.action a) ![v],
    fun a => M.base.operation (.atom a) (fun i => i.elim0), M.point⟩

def modalModels (L : ModalMu.Signature) : PointedModel () (modalSignature L) ⥤ ModalMu.Model L where
  obj := forgetModal
  map h := ⟨congrArg forgetModal h.down⟩

/-- Every pointed modal frame expands with the same carrier, point, atoms and steps. -/
def expandModal {L : ModalMu.Signature} (M : ModalMu.Model L) : PointedModel () (modalSignature L) where
  base :=
    { carrier := fun _ => M.World
      nonempty := fun _ => ⟨M.point⟩
      operation := fun op => match op with
        | .atom a => fun _ => M.valuation a
        | .action a => fun args => {w | M.step a w (args 0)} }
  point := M.point

end Silmaril.Logic.Matching.FixedPoint
