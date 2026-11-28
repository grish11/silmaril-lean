module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Terminator)
open Silmaril.MLIR.Pure (Code)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM (shape)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input Γ : List Width} {saved carried result : Width} {extra : List Width}

theorem Prefix.wrap_eval (leading : Prefix Input Γ)
    (tail : Block TargetOp (Label saved carried result extra) Γ [result]) (input : Env Input) :
    (leading.wrap tail).eval evalOp (fun term env => Terminator.eval env term) input =
      tail.eval evalOp (fun term env => Terminator.eval env term) (leading.eval input) := by
  induction leading with
  | nil => rfl
  | snoc prior op operands ih =>
    rw [Prefix.wrap, ih]
    rfl

theorem Prefix.wrap_targets {Γ newExtra : List Width}
    (leading : Saved.Prefix Input Γ) (tail : Block TargetOp (Label saved carried result newExtra) Γ [result]) :
    (shape.ofBlock (leading.wrap tail)).target = (shape.ofBlock tail).target := by
  induction leading with
  | nil => rfl
  | snoc prior op operands ih => exact ih (.letOp op operands tail)

theorem splitPrefix?_wrap {widths : List Width}
    {code : Block TargetOp (Label saved carried result extra) Input [result]}
    {leading : Prefix Input (widths ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) (widths ++ Input) [result]}
    (split : splitPrefix? code widths = some (leading, tail)) :
    leading.wrap tail = code := by
  induction widths with
  | nil =>
    cases split
    rfl
  | cons width rest ih =>
    obtain ⟨⟨prior, body⟩, found, edited⟩ := Option.bind_eq_some_iff.mp split
    cases body with
    | terminator => cases edited
    | @letOp _ _ actual op operands suffix =>
      by_cases same : actual = width
      · subst actual
        simp at edited
        obtain ⟨rfl, rfl⟩ := edited
        exact ih found
      · simp [same] at edited

/-- Appending a saved definition to the exact prefix gives the next
split, independently of the lifted suffix. -/
theorem splitPrefix?_snoc {widths args : List Width} {w : Width} {newExtra : List Width}
    {code : Block TargetOp (Label saved carried result extra) Input [result]}
    {leading : Prefix Input (widths ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) (widths ++ Input) [result]}
    (split : splitPrefix? code widths = some (leading, tail))
    (op : TargetOp args w) (operands : Silmaril.MLIR.Pure.Operands (widths ++ Input) args)
    (suffix : Block TargetOp (Label saved carried result newExtra) (w :: (widths ++ Input)) [result]) :
    splitPrefix? (leading.wrap (.letOp op operands suffix)) (w :: widths) =
      some (.snoc leading op operands, suffix) := by
  have rewrap : ∀ {widths : List Width}
        {code : Block TargetOp (Label saved carried result extra) Input [result]}
        {leading : Prefix Input (widths ++ Input)}
        {tail : Block TargetOp (Label saved carried result extra) (widths ++ Input) [result]},
        splitPrefix? code widths = some (leading, tail) →
        ∀ (body : Block TargetOp (Label saved carried result newExtra) (widths ++ Input) [result]),
          splitPrefix? (leading.wrap body) widths = some (leading, body) := by
    intro widths
    induction widths with
    | nil =>
      intro code leading tail accepted body
      cases accepted
      rfl
    | cons width rest ih =>
      intro code leading tail accepted body
      obtain ⟨⟨prior, inner⟩, found, edited⟩ := Option.bind_eq_some_iff.mp accepted
      cases inner with
      | terminator => cases edited
      | @letOp _ _ actual earlier refs next =>
        by_cases same : actual = width
        · subst actual
          simp at edited
          obtain ⟨rfl, rfl⟩ := edited
          simp [Prefix.wrap, splitPrefix?, ih found (.letOp earlier refs body)]
        · simp [same] at edited
  simp [splitPrefix?, rewrap split (.letOp op operands suffix)]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved
