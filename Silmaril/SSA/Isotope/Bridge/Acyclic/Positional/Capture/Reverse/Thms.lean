module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Plan
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Grammar

/-! # Certification and exact LetCase comparison for captured reification -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d : Nat} {β : BoundCtx τ d} {L : LCtx τ} {A : τ} {R : List τ} {n : Nat}

/-- The numbering of a nonempty plan passes the existing rank checker. -/
theorem Plan.checked (p : Plan Φ β L (A :: R)) : p.toTable.check = true :=
  plan_check_proof p

/-- Rendering the checked table tree at any capture scope agrees with the
actual forward compiler at the same local label. -/
theorem tableTree_render (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    (tableTree p ok i).render s = p.compileAt ok i s :=
  tableTree_render_proof p ok i s

/-- Numbering a tree preserves the rendering at its new front row. -/
theorem Tree.build_compile (t : Tree Φ β L A) (p : Plan Φ β L R)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    (t.build p).plan.toTable.compileAt (t.build p).plan.checked 0 s = t.render s :=
  tree_build_compile_proof t p _ s

theorem Program.toTable_checked (p : Program Φ β L) : p.toTable.check = true :=
  p.build.plan.checked

theorem Program.toTable_render (p : Program Φ β L) :
    p.toTable.toFiniteExit p.toTable_checked 0 p.entry = p.toFiniteExit :=
  program_toFiniteExit_proof p p.toTable_checked

theorem tableProgram_render (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    (tableProgram p ok i a).toFiniteExit = p.toFiniteExit ok i a :=
  tableProgram_render_proof p ok i a

/-- Every actual output of the captured LetCase lowering has a grammar witness. -/
def tableGrammar (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) : ResultGrammar (p.toLetCase ok i a) :=
  ⟨tableProgram p ok i a, congrArg (fun t => t.encode.toLetCase) (tableProgram_render p ok i a)⟩

/-- Recover the grammar witness at the checked forward entry point. -/
def tableGrammarOfSuccess (p : Table Φ β L n) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) {term : Operand Φ β (Region.packedExitType L)}
    (result : p.toLetCase? i a = some term) : ResultGrammar term := by
  unfold Table.toLetCase? at result
  split at result
  · rename_i ok
    obtain rfl := Option.some.inj result
    exact tableGrammar p ok i a
  · contradiction

/-- Reverse a typed grammar witness into a checked positional table. The
entry is zero, and its ambient context and outward positions are unchanged. -/
def ResultGrammar.toTable {term : Operand Φ β (Region.packedExitType L)} (g : ResultGrammar term) :
    CheckedTable Φ β L :=
  ⟨_, g.val.toTable, g.val.toTable_checked, g.val.entry⟩

/-- Forward lowering of the newly numbered table returns the exact
witnessed term. The equation compares packed LetCase syntax. -/
theorem ResultGrammar.toTable_toLetCase {term : Operand Φ β (Region.packedExitType L)}
    (g : ResultGrammar term) : g.toTable.toLetCase = term :=
  (congrArg (fun t => t.encode.toLetCase) g.val.toTable_render).trans g.property

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
