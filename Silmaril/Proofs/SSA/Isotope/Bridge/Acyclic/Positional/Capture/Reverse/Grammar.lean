module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

set_option backward.isDefEq.respectTransparency false

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d : Nat} {β : BoundCtx τ d} {L : LCtx τ} {A : τ}
  {k : Nat} {types : Fin k → τ}

private theorem targetTree_render (t : Target types L A) {labels : List (Fin k)}
    (edge : ∀ j ∈ t.locals, j ∈ labels) (next : LocalTrees (Φ := Φ) (β := β) (L := L) types labels)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    (targetTree t edge next).render s =
      t.compile edge s (fun j h _ _ scope => (next j h).render scope) := by
  cases t <;> rfl

private theorem blockTree_render (b : Block Φ β types L A)
    (next : LocalTrees (Φ := Φ) (β := β) (L := L) types b.locals)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    (blockTree b next).render s =
      b.compile s (fun j h _ _ scope => (next j h).render scope) := by
  cases b <;> simp only [blockTree, Tree.render, Block.compile, targetTree_render]
  all_goals rfl

theorem tableTree_render_proof {n : Nat} (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    (tableTree p ok i).render s = p.compileAt ok i s := by
  rw [tableTree.eq_def, Table.compileAt.eq_def, blockTree_render]
  congr 1
  funext j edge m' γ' scope
  exact tableTree_render_proof p ok j scope
termination_by p.rank i
decreasing_by exact p.decreases ok edge

theorem tableProgram_render_proof {n : Nat} (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    (tableProgram p ok i a).toFiniteExit = p.toFiniteExit ok i a := by
  unfold tableProgram Program.toFiniteExit Table.toFiniteExit
  exact congrArg (FiniteExit.join (.br a)) (tableTree_render_proof p ok i .base)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
