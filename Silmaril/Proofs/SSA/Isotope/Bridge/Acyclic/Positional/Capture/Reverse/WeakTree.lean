module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open LambdaSSA.Acyclic LambdaSSA.Acyclic.Positional.Capture
open LambdaSSA.Acyclic.Positional.Capture.Reverse
open LambdaSSA.Semantics (Env extend extend_zero)
open LambdaSSA.Semantics.Interaction
open Morphism.CaseSSA (erase)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree iterate_fixpoint diverge_bind)

universe u v w x

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
  {n m k : Nat} {β : BoundCtx τ n} {γ : BoundCtx τ m} {R : Fin k → τ} {L : LCtx τ} {A : τ}
  {Events : Type w → Type w} {α : Type x} (raw : Primitive Events Φ α)

private abbrev render (c : FiniteExit Φ L γ) : LambdaSSA.Tm Φ :=
  erase c.encode.toLetCase.1

private def Agrees (s : Scope β γ) (base current : Env α) : Prop :=
  ∀ i : Fin n, current (s.renaming.toFun i).val = base i.val

omit [TypeFormers τ] in
private theorem agrees_skip (s : Scope β γ) {base current : Env α} (agree : Agrees s base current)
    (T : τ) (v : Value α) : Agrees (.skip s T) base (extend current v) :=
  fun i => agree i

private theorem scope_tree (s : Scope β γ) {base current : Env α} (agree : Agrees s base current)
    {B : τ} (a : Operand Φ (β.snoc A) B) (v : Value α) :
    term raw (extend current v) (erase (s.operand a).1) =
      term raw (extend base v) (erase a.1) :=
  FlatLetCase.operand_rename_tree raw (s.renaming.up A).toFun (Fin.cases rfl fun i => agree i)

private abbrev packed (out : Transfer α) : Tree Events (Value α) :=
  pure (Region.packedExitValue out.1 out.2)

private theorem target_tree (t : Target R L A) {labels : List (Fin k)}
    (edge : ∀ j ∈ t.locals, j ∈ labels) (s : Scope β γ)
    (next : LocalContinuations β R L Φ labels)
    (current : Env α) (v : Value α) (run : BlockInput α k → Tree Events (Value α))
    (calls : ∀ j (h : j ∈ labels), term raw (extend current v) (render (next j h s)) = run (j, v)) :
    term raw (extend current v) (render (t.compile edge s next)) =
      Sum.elim packed run (splitTransfer k (t.index, v)) := by
  cases t with
  | «local» j =>
    simpa only [Target.compile, Target.index, splitTransfer, j.isLt, ↓reduceDIte, Sum.elim_inr] using
      calls j (edge j (by simp [Target.locals]))
  | @exit i A h =>
    have outside : ¬ k + i < k := by omega
    simp only [Target.compile, render, FiniteExit.encode, Code.toLetCase, Target.index, splitTransfer, outside,
      ↓reduceDIte, Nat.add_sub_cancel_left, Sum.elim_inl]
    rw [FlatLetCase.tag_tree]
    simp only [erase, term, pure_bind]
    rfl

private theorem block_tree (b : Block Φ β R L A) (s : Scope β γ)
    (base current : Env α) (agree : Agrees s base current) (v : Value α)
    (next : LocalContinuations β R L Φ b.locals)
    (run : BlockInput α k → Tree Events (Value α))
    (calls : ∀ j (h : j ∈ b.locals) value,
      term raw (extend (extend current v) value) (render (next j h (.skip s A))) = run (j, value)) :
    term raw (extend current v) (render (b.compile s next)) =
      (region raw (extend base v) b.toSSA >>= fun p => Sum.elim packed run (splitTransfer k p)) := by
  cases b with
  | jump a t =>
    simp only [Block.compile, render, FiniteExit.encode, Code.toLetCase, erase, term, Block.toSSA,
      region, bind_assoc, pure_bind]
    rw [scope_tree raw s agree a v]
    exact bind_congr fun value => target_tree raw t (fun _ h => h) (.skip s A) next _ value run
      (fun j h => calls j h value)
  | case a l r =>
    simp only [Block.compile, render, FiniteExit.encode, Code.toLetCase, erase, term, Block.toSSA,
      region, bind_assoc]
    rw [scope_tree raw s agree a v]
    apply bind_congr
    intro value
    cases value <;> simp only [diverge_bind]
    case inl x =>
      simpa only [render, pure_bind, extend_zero] using target_tree raw l (fun _ h => List.mem_append_left _ h)
        (.skip s A) next _ x run (fun j h => calls j h x)
    case inr y =>
      simpa only [render, pure_bind, extend_zero] using target_tree raw r (fun _ h => List.mem_append_right _ h)
        (.skip s A) next _ y run (fun j h => calls j h y)

private noncomputable abbrev step {size : Nat} (p : Table Φ β L size) (base : Env α)
    (s : BlockInput α (size + 1)) : Tree Events (Transfer α ⊕ BlockInput α (size + 1)) :=
  region raw (extend base s.2) (p.block s.1).toSSA >>= fun out => pure (splitTransfer (size + 1) out)

private theorem row_tree {size : Nat} (p : Table Φ β L size) (ok : p.check = true)
    (base : Env α) (i : Fin (size + 1)) {m : Nat} {γ : BoundCtx τ m}
    (s : Scope β γ) (current : Env α) (agree : Agrees s base current) (v : Value α) :
    term raw (extend current v) (render (p.compileAt ok i s)) =
      (iter (step raw p base) (i, v) >>= packed) := by
  rw [Table.compileAt, block_tree raw (p.block i) s base current agree v
    (fun j _ _ _ sc => p.compileAt ok j sc) (fun q => iter (step raw p base) q >>= packed)
    (fun j edge value => row_tree p ok base j (.skip s (p.types i)) (extend current v)
      (agrees_skip s agree (p.types i) v) value)]
  rw [congrFun (iterate_fixpoint (step raw p base)) (i, v)]
  simp only [bind_assoc, pure_bind]
  exact bind_congr fun q => by cases splitTransfer (size + 1) q <;> simp only [Sum.elim_inl, Sum.elim_inr, pure_bind]
termination_by p.rank i
decreasing_by exact p.decreases ok edge

theorem toLetCase_tree (c : CheckedTable Φ β L) (base : Env α) :
    term raw base (erase c.toLetCase.1) =
      (region raw base c.toSSA >>= fun out => pure (Region.packedExitValue out.1 out.2)) := by
  change term raw base (render (c.table.toFiniteExit c.checked 0 c.entry)) = _
  simp only [Table.toFiniteExit, render, FiniteExit.encode, Code.toLetCase, erase, term,
    CheckedTable.toSSA, Table.toSSA, Table.entry, region, bind_assoc, pure_bind]
  exact bind_congr fun v => row_tree raw c.table c.checked base 0 .base base (fun _ => rfl) v

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse
