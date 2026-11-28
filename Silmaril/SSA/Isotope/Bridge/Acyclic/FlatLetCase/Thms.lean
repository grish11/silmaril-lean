module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Scoped.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Tree
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Typed

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase

open Positional
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction
open Morphism.CaseSSA (erase)

universe u v w x
variable {Φ : Type v} {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {blocks exits n : Nat} {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits n}

/-- Encoding an outward position leaves operand evaluation intact. -/
theorem tag_tree {Events : Type w → Type w} {α : Type x} (raw : Primitive Events Φ α)
    {L : LCtx τ} {A : τ} {i : Nat} (hi : At L i A) (a : Operand Φ β A) (env : Env α) :
    term raw env (erase (FiniteExit.tag L i hi a).1) =
      (term raw env (erase a.1) >>= fun v => pure (Region.packedExitValue i v)) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase.tag_tree raw hi a env

/-- The erased operand only reads the image of its in-scope indices. -/
theorem operand_rename_tree {Events : Type w → Type w} {α : Type x}
    (raw : Primitive Events Φ α) {m : Nat} {a : LetCase.LocallyNameless.Tm Empty Φ n}
    (ρ : Fin n → Fin m) {env env' : Env α} (agree : ∀ i, env' (ρ i).val = env i.val) :
    term raw env' (erase (a.rename ρ)) = term raw env (erase a) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase.operand_rename raw ρ agree

/-- Exact flat typing supplies witnesses of the literal written operands. -/
theorem witness_nonempty (h : g.HasType β R D) : Nonempty (Witness g β R D) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase.witness_nonempty h

/-- Expand the well-typed entry and its reachable rows. The entire typed
table remains the source of the proof and interpreter. -/
noncomputable def toLetCaseReachable (h : g.HasType β R D) (ranked : entryCheck g = true) :
    Operand Φ β (Region.packedExitType (List.ofFn D)) :=
  (compileReachable (witness_nonempty h).some ranked).toLetCase

/-- Expand the actual written table when the finite rank check succeeds.
Selection of operand derivations from propositional typing is noncomputable. -/
noncomputable def toLetCase (h : g.HasType β R D) (ranked : Rank.check (localTargets g) = true) :
    Operand Φ β (Region.packedExitType (List.ofFn D)) :=
  toLetCaseReachable h (Rank.checkFrom_of_check (localTargets g) (targets g.entry) ranked)

/-- Rank induction removes flat feedback while preserving the weak tree,
using the same request and reply continuations and the existing exit tags. -/
theorem compileReachable_tree {Events : Type w → Type w} {α : Type x} (raw : Primitive Events Φ α)
    (w : Witness g β R D) (ranked : entryCheck g = true) (env : Env α) :
    term raw env (erase (compileReachable w ranked).toLetCase.1) =
      (region raw env g.erase >>= fun out => pure (Region.packedExitValue out.1 out.2)) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase.compileReachable_tree raw w ranked env

theorem toLetCaseReachable_tree {Events : Type w → Type w} {α : Type x} (raw : Primitive Events Φ α)
    (h : g.HasType β R D) (ranked : entryCheck g = true) (env : Env α) :
    term raw env (erase (toLetCaseReachable h ranked).1) =
      (region raw env g.erase >>= fun out => pure (Region.packedExitValue out.1 out.2)) :=
  compileReachable_tree raw (witness_nonempty h).some ranked env

theorem compile_tree {Events : Type w → Type w} {α : Type x} (raw : Primitive Events Φ α)
    (w : Witness g β R D) (ranked : Rank.check (localTargets g) = true) (env : Env α) :
    term raw env (erase (compile w ranked).toLetCase.1) =
      (region raw env g.erase >>= fun out => pure (Region.packedExitValue out.1 out.2)) :=
  compileReachable_tree raw w (Rank.checkFrom_of_check (localTargets g) (targets g.entry) ranked) env

theorem toLetCase_tree {Events : Type w → Type w} {α : Type x} (raw : Primitive Events Φ α)
    (h : g.HasType β R D) (ranked : Rank.check (localTargets g) = true) (env : Env α) :
    term raw env (erase (toLetCase h ranked).1) =
      (region raw env g.erase >>= fun out => pure (Region.packedExitValue out.1 out.2)) :=
  compile_tree raw (witness_nonempty h).some ranked env

section Denotation

open Isotope.Semantics (InstructionModel BoundEnv encodeValue)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues Compatible ModelTree)
open LetCase.LocallyNameless (Derivation)

variable {κ : Type (w + 1)} [AtomValues κ] {Events : Type w → Type w}
  {F : Type v} [HasTy F (Ty κ)] {slots : Nat} {δ : BoundCtx (Ty κ) slots}
  {A : Ty κ} {t : LetCase.LocallyNameless.Tm Empty F slots}

local notation "C" => AtomValues.carrier (κ := κ)

/-- The native typed LetCase denotation encodes to the existing erased
weak tree under pointwise input and primitive agreement. -/
theorem denote_tree (M : InstructionModel (Ty.denote C) F (ModelTree Events))
    (raw : Primitive Events F (Sigma C)) (compatible : Compatible M raw)
    (d : Derivation F (.nil : Ctx Empty (Ty κ)) δ t A)
    (ρ : BoundEnv (Ty.denote C) δ) (env : Env (Sigma C))
    (agree : ∀ i, env i.val = encodeValue C (δ.get i) (ρ i)) :
    (d.denote (Ty.denote C) M (fun x => x.elim) ρ >>= fun a => pure (encodeValue C A a)) =
      term raw env (erase t) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase.denote_tree M raw compatible d ρ env agree

end Denotation

end Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase
