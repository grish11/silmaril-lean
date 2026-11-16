module

public import Silmaril.Logic.Reachability.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability
open CategoryTheory

/-- Any nonempty transition system is realized by actual matching operations. -/
def relationalSignature (Atom : Type) : Signature () :=
  ⟨Matching.FixedPoint.modalSignature ⟨Atom, Unit⟩, Matching.FixedPoint.ModalOperation.action ()⟩

def relationalModel {Atom W : Type} [Nonempty W] (R : W → W → Prop) (V : Atom → Set W) :
    Model () (relationalSignature Atom) where
  carrier := fun _ => W
  nonempty := fun _ => inferInstance
  operation := fun op => match op with
    | .atom a => fun _ => V a
    | .action _ => fun args => {w | R w (args 0)}

def atom {Atom : Type} (a : Atom) :
    Matching.FirstOrder.Pattern (relationalSignature Atom).algebra (k := 0) Fin.elim0 () :=
  .app (.atom a) (fun i => i.elim0)

def atomRule {Atom : Type} (mode : Mode) (pre post : Atom) : Sentence () (relationalSignature Atom) :=
  ⟨0, Fin.elim0, mode, atom pre, atom post⟩

theorem relational_step {Atom W : Type} [Nonempty W] (R : W → W → Prop) (V : Atom → Set W) :
    step () (relationalModel R V) = R := rfl

theorem atom_denote {Atom W : Type} [Nonempty W] (R : W → W → Prop) (V : Atom → Set W)
    (a : Atom) (v : (i : Fin 0) → (relationalModel R V).carrier (Fin.elim0 i)) : (relationalModel R V).denote v (atom a) = V a := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨_, _, ha⟩
    exact ha
  · intro ha
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), ha⟩

theorem atomRule_iff {Atom W : Type} [Nonempty W] (R : W → W → Prop) (V : Atom → Set W)
    (mode : Mode) (pre post : Atom) :
    (atomRule mode pre post).Satisfies () (relationalModel R V) ↔
      ∀ w, w ∈ V pre → mode.Holds R (fun x => x ∈ V post) w := by
  change (∀ v w, w ∈ (relationalModel R V).denote v (atom pre) →
    mode.Holds (step () (relationalModel R V))
      (fun x => x ∈ (relationalModel R V).denote v (atom post)) w) ↔ _
  simp only [atom_denote, relational_step]
  exact ⟨fun h => h (fun i => i.elim0), fun h _ => h⟩

end Silmaril.Logic.Reachability
