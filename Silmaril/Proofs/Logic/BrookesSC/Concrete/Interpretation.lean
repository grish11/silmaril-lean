module

public import Silmaril.Logic.BrookesSC.Concrete.Defs
public import Silmaril.Semantics.Brookes.Thms

public section

namespace Silmaril.Proofs.Logic.BrookesSC.Concrete

open Silmaril.Logic.BrookesSC Silmaril.Logic.BrookesSC.Concrete Silmaril.Semantics.Brookes

universe u

variable {W : World.{u}} {A B : Type u}

theorem bind_mono {x y : Behavior (Store W) A} {k l : A → Behavior (Store W) B}
    (h : Includes x y) (hk : ∀ a, Includes (k a) (l a)) : Includes (x.bind k) (y.bind l) := by
  intro trace value mem
  obtain ⟨left, right, reply, hl, hr, hd⟩ := Behavior.bind_accepts_iff.mp mem
  exact Behavior.bind_accepts_iff.mpr ⟨left, right, reply, h hl, hk reply hr, hd⟩

variable [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread]

theorem primitive_bind_accepts_iff (p : Primitive W) (next : p.Reply → Behavior (Store W) A)
    (trace : Trace (Store W)) (value : A) :
    ((primitive p).bind next).accepts trace value ↔
      ∃ s t reply tail, Store.step p s = some (reply, t) ∧ (next reply).accepts tail value ∧
        Reduces ([(s, t)] ++ tail) trace := by
  rw [Behavior.bind_accepts_iff]
  constructor
  · rintro ⟨left, tail, reply, hleft, htail, hd⟩
    obtain ⟨s, t, hstep, hgen⟩ := Behavior.atomic_accepts_iff.mp hleft
    exact ⟨s, t, reply, tail, hstep, htail, (hgen.append_right tail).trans hd⟩
  · rintro ⟨s, t, reply, tail, hstep, htail, hd⟩
    exact ⟨[(s, t)], tail, reply, Behavior.atomic_accepts_iff.mpr ⟨s, t, hstep, .refl _⟩, htail, hd⟩

end Silmaril.Proofs.Logic.BrookesSC.Concrete
