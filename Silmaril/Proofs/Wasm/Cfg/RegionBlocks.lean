module

public import Silmaril.Proofs.Wasm.Cfg.Region
public import Silmaril.Wasm.Cfg.Block.Thms

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem expression_flatMap (segs : List Segment) :
    expression (segs.flatMap Segment.instrs) = (segs.map fun sg => expression sg.instrs).flatten := by
  induction segs with
  | nil => rfl
  | cons sg segs ih => simp [expression] at ih ⊢; exact ih

theorem run_iff_segRun : ∀ {segs : List Segment} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {o : Out}, Run P host s f vs (expression (segs.flatMap Segment.instrs)) s' f' o ↔
      SegRun P host s f vs segs s' f' o
  | [], s, s', f, f', vs, o => by
    constructor
    · intro h; obtain ⟨rfl, rfl, rfl⟩ := run_nil_inv h; exact .nil
    · intro h; cases h; exact .nil
  | sg :: segs, s, s', f, f', vs, o => by
    have e : expression ((sg :: segs).flatMap Segment.instrs) =
        expression sg.instrs ++ expression (segs.flatMap Segment.instrs) := by
      simp [expression]
    rw [e]
    constructor
    · intro h
      obtain ⟨s₁, f₁, o₁, h₁, h₂⟩ := run_split h rfl
      cases o₁ with
      | normal us => exact .next h₁ (run_iff_segRun.1 h₂)
      | br l us => obtain ⟨rfl, rfl, rfl⟩ := h₂; exact .exit h₁ (by simp)
      | ret us => obtain ⟨rfl, rfl, rfl⟩ := h₂; exact .exit h₁ (by simp)
      | trap => obtain ⟨rfl, rfl, rfl⟩ := h₂; exact .exit h₁ (by simp)
      | throw a => obtain ⟨rfl, rfl, rfl⟩ := h₂; exact .exit h₁ (by simp)
      | tail vs a c => obtain ⟨rfl, rfl, rfl⟩ := h₂; exact .exit h₁ (by simp)
      | tailNull vs c => obtain ⟨rfl, rfl, rfl⟩ := h₂; exact .exit h₁ (by simp)
    · intro h
      cases h with
      | next h₁ hk => exact run_append h₁ (run_iff_segRun.2 hk)
      | exit h₁ ho =>
        refine run_append h₁ ?_
        cases o with
        | normal us => exact absurd rfl (ho us)
        | _ => exact ⟨rfl, rfl, rfl⟩

/-- A sequence runs exactly along its canonical basic blocks. -/
theorem run_iff_blocks {is : List Instr} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {o : Out} :
    Run P host s f vs (expression is) s' f' o ↔ SegRun P host s f vs (segment is) s' f' o := by
  have := (segment_isSegmentation is).1
  conv_lhs => rw [← this]
  exact run_iff_segRun

end Silmaril.Wasm.Cfg.Proofs.Region
