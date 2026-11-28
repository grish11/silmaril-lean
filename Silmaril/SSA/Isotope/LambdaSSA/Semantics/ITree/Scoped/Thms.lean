module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Scoped

/-! # Renaming erased flat code under in-scope environment agreement -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction

variable {E : Type w → Type w} {Φ : Type v} {α : Type u} {n labels : Nat}
variable (instr : Primitive E Φ α) {env env' : Env α}

/-- An erased scoped term depends only on its finite context prefix. -/
theorem term_tree_of_agree (t : LetCase.LocallyNameless.Tm Empty Φ n)
    (agree : ∀ i : Fin n, env' i.val = env i.val) :
    term instr env' (Morphism.CaseSSA.erase t) = term instr env (Morphism.CaseSSA.erase t) := by
  simpa only [Tm.rename_id] using Proofs.SSA.Isotope.LambdaSSA.Interaction.erase_term_rename
    instr t (ρ := id) agree

/-- A value renaming preserves the whole tree of a flat region when its
environments agree on the images of the in-scope indices. Agreement lifts
through each local binder. -/
theorem flat_rename_tree (r : Flat Φ labels n) {ρ : Nat → Nat}
    (agree : ∀ i : Fin n, env' (ρ i.val) = env i.val) :
    region instr env' (r.erase.renameVars ρ) = region instr env r.erase :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.flat_rename_tree instr r agree

/-- Erased flat code observes only the bounded prefix of its environment. -/
theorem flat_tree_of_agree (r : Flat Φ labels n)
    (agree : ∀ i : Fin n, env' i.val = env i.val) :
    region instr env' r.erase = region instr env r.erase := by
  simpa only [Region.renameVars_id] using flat_rename_tree instr r (ρ := id) agree

/-- Entry and every local block preserve weak execution when the shared
in-scope environment agrees. This includes feedback through the blocks. -/
theorem cfg_tree_of_agree {blocks exits : Nat} (g : FiniteCFG Φ blocks exits n)
    (agree : ∀ i : Fin n, env' i.val = env i.val) :
    region instr env' g.erase = region instr env g.erase :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.cfg_tree_of_agree instr g agree

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction
