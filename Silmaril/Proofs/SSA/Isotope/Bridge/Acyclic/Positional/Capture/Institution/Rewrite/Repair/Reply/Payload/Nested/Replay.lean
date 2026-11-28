module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested

open Isotope.LetCase.LocallyNameless (Equiv HasType Tm)
open LambdaSSA.Region (packedExitType)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

private theorem inner_replay {L : List Sorts} (a : Inner L) {n : Nat}
    (β : BoundCtx Sorts n) (i : Fin n) (h : β.get i = Bit) :
    Equiv false Γ₀ (β.snoc Bit) (a.operand β i h).1
      (a.normal.render.operand β i h).1 (packedExitType L) :=
  .case (.refl .bv)
    (a.whenFalse.replay_at a.whenFalse.emits ((β.snoc Bit).snoc U) i.succ.succ h)
    (a.whenTrue.replay_at a.whenTrue.emits ((β.snoc Bit).snoc U) i.succ.succ h)

private theorem prefix_replay {L : List Sorts} (req bound : Bool) (l r : Inner L) (es : List Bool)
    {n : Nat} (β : BoundCtx Sorts n) (i : Fin n) (h : β.get i = Bit) :
    Equiv false Γ₀ β (requestWithPrefix req bound l r es β i h).1
      (requestWithPrefix req false l.normal.render r.normal.render es β i h).1 (packedExitType L) := by
  induction es generalizing n with
  | nil => exact request_replay req bound _ _ _ _ (inner_replay l β i h) (inner_replay r β i h)
  | cons _ _ ih => exact .let₁ (.refl (.op .unit)) (ih (β.snoc U) i.succ h)

private theorem outer_replay {L : List Sorts} (a : Outer L) :
    Equiv false Γ₀ (.snoc .nil Bit) a.operand.1 a.normal.render.operand.1 (packedExitType L) := by
  cases a with
  | finish a => exact a.replay_at a.emits (.snoc .nil Bit) 0 rfl
  | request es req bound l r => exact prefix_replay req bound l r es (.snoc .nil Bit) 0 rfl

theorem entry_replay_proof {L : List Sorts} (p : ProgramBody L) :
    Equiv false Γ₀ .nil p.entry.1 p.normal.render.entry.1 (packedExitType L) :=
  request_replay p.request p.bound _ _ _ _ (outer_replay p.left) (outer_replay p.right)

theorem derive_normal_proof (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (h : p.normal = q.normal) : Derivable false (equation H L p q) := by
  have replay := entry_replay_proof p
  rw [h] at replay
  exact .let₁ (replay.trans (entry_replay_proof q).symm)
    (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType)

theorem derive_render_proof (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Derivable false (equation H L p p.normal.render) :=
  .let₁ (entry_replay_proof p) (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested
