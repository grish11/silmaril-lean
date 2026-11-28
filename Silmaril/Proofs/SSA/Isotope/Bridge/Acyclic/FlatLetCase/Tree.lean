module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Scoped.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open LambdaSSA.Acyclic LambdaSSA.Acyclic.FlatLetCase LambdaSSA.Acyclic.Positional
open LambdaSSA.Acyclic.Positional.Capture (Scope)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction
open LetCase.LocallyNameless (Derivation)
open Morphism.CaseSSA (erase)
open SSA.FiniteSum (append)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree iterate_fixpoint diverge_bind)

universe u v w x
variable {Φ : Type v} {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {blocks exits n m : Nat} {β : BoundCtx τ n} {γ : BoundCtx τ m}
  {R : Fin blocks → τ} {D : Fin exits → τ}
  {Events : Type w → Type w} {α : Type x}

private theorem body_nonempty {labels : Nat} {L : Fin labels → τ} {t : Flat Φ labels m}
    (h : Flat.HasType L γ t) : Nonempty (Body Φ L γ t) := by
  induction h with
  | br h => obtain ⟨a⟩ := Derivation.ofHasType h; exact ⟨.br _ ⟨_, a⟩⟩
  | let₁ h _ ih => obtain ⟨a⟩ := Derivation.ofHasType h; obtain ⟨b⟩ := ih; exact ⟨.let₁ ⟨_, a⟩ b⟩
  | let₂ h _ ih => obtain ⟨a⟩ := Derivation.ofHasType h; obtain ⟨b⟩ := ih; exact ⟨.let₂ ⟨_, a⟩ b⟩
  | case h _ _ ihl ihr =>
    obtain ⟨e⟩ := Derivation.ofHasType h
    obtain ⟨l⟩ := ihl
    obtain ⟨r⟩ := ihr
    exact ⟨.case ⟨_, e⟩ l r⟩

theorem witness_nonempty {g : FiniteCFG Φ blocks exits n} (h : g.HasType β R D) :
    Nonempty (Witness g β R D) :=
  ⟨⟨(body_nonempty h.entry).some, fun i => (body_nonempty (h.block i)).some⟩⟩

variable (raw : Primitive Events Φ α)

theorem tag_tree {L : LCtx τ} {A : τ} {i : Nat} (hi : At L i A)
    (a : Operand Φ γ A) (env : Env α) :
    term raw env (erase (FiniteExit.tag L i hi a).1) =
      (term raw env (erase a.1) >>= fun v => pure (Region.packedExitValue i v)) := by
  induction L generalizing i with
  | nil => cases i <;> cases hi
  | cons T rest ih =>
    cases i with
    | zero =>
      have eq : T = A := Option.some.inj hi
      subst T
      rfl
    | succ i =>
      simp only [FiniteExit.tag, erase, term, Region.packedExitValue, ih hi, bind_assoc, pure_bind]

/-- There is no dependence on indices outside the source term's bounded scope. -/
theorem operand_rename {a : LetCase.LocallyNameless.Tm Empty Φ n}
    (ρ : Fin n → Fin m) {env env' : Env α}
    (agree : ∀ i, env' (ρ i).val = env i.val) :
    term raw env' (erase (a.rename ρ)) = term raw env (erase a) := by
  let lift := fun i => if h : i < n then (ρ ⟨i, h⟩).val else i
  have indices (i : Fin n) : (ρ i).val = lift i.val := by simp [lift, i.isLt]
  have h := flat_rename_tree raw (Flat.br (0 : Fin 1) a) (ρ := lift)
    (fun i => (congrArg env' (indices i)).symm.trans (agree i))
  have projected := congrArg (fun tree => tree >>= fun p : Transfer α => pure p.2) h
  simpa only [Flat.erase, Region.renameVars, region, bind_assoc, pure_bind, bind_pure,
    Morphism.CaseSSA.erase_rename ρ lift indices a] using projected

private def Agrees (s : Scope β γ) (base current : Env α) : Prop :=
  ∀ i : Fin n, current (s.renaming.toFun i).val = base i.val

omit [TypeFormers τ] in
private theorem agrees_skip (s : Scope β γ) {base current : Env α} (h : Agrees s base current)
    (A : τ) (v : Value α) : Agrees (.skip s A) base (extend current v) := fun i => h i

private theorem weaken_tree (s : Scope β γ) {base current : Env α} (agree : Agrees s base current)
    {A B : τ} (a : Operand Φ (β.snoc A) B) (v : Value α) :
    term raw (extend current v) (erase (weakenPacket s a).1) =
      term raw (extend base v) (erase a.1) :=
  operand_rename raw (s.renaming.up A).toFun (Fin.cases rfl fun i => agree i)

private theorem operand_cast {A B : τ} (eq : A = B) (a : Operand Φ γ A) :
    (eq ▸ a : Operand Φ γ B).1 = a.1 := by
  cases eq
  rfl

private theorem body_tree {t : Flat Φ (blocks + exits) m} (b : Body Φ (append R D) γ t)
    (s : Scope β γ) (base current : Env α) (agree : Agrees s base current)
    (next : ∀ j ∈ targets t, Operand Φ (β.snoc (R j)) (Region.packedExitType (List.ofFn D)))
    (run : BlockInput α blocks → Tree Events (Value α))
    (calls : ∀ j edge v, term raw (extend base v) (erase (next j edge).1) = run (j, v)) :
    term raw current (erase (compileBody b s next).toLetCase.1) =
      (region raw current t.erase >>= fun p =>
        Sum.elim (fun out => pure (Region.packedExitValue out.1 out.2)) run (splitTransfer blocks p)) := by
  induction b generalizing current with
  | br i a =>
    revert a next
    refine Fin.addCases (fun j a next calls => ?_) (fun j a next calls => ?_) i
    · simp only [compileBody, compileJump, Fin.addCases_left, Code.toLetCase, erase, term,
        Flat.erase, region, bind_assoc, pure_bind, operand_cast]
      apply bind_congr
      intro v
      rw [weaken_tree raw s agree, calls]
      simp [splitTransfer, j.isLt]
    · simp only [compileBody, compileJump, Fin.addCases_right, Code.toLetCase, Flat.erase, region,
        bind_assoc, pure_bind]
      rw [tag_tree, operand_cast]
      have outside : ¬ blocks + j.val < blocks := by omega
      simp only [splitTransfer, Fin.val_natAdd, outside, ↓reduceDIte, Nat.add_sub_cancel_left, Sum.elim_inl]
  | let₁ a b ih =>
    simp only [compileBody, Code.toLetCase, erase, term, Flat.erase, region, bind_assoc]
    exact bind_congr fun v => ih (.skip s _) (extend current v) (agrees_skip s agree _ v) next calls
  | let₂ a b ih =>
    simp only [compileBody, Code.toLetCase, erase, term, Flat.erase, region, bind_assoc]
    apply bind_congr
    intro v
    cases v <;> simp only [diverge_bind]
    case pair x y =>
      exact ih (.skip (.skip s _) _) (extend (extend current x) y)
        (agrees_skip _ (agrees_skip s agree _ x) _ y) next calls
  | case e left right ihl ihr =>
    simp only [compileBody, Code.toLetCase, erase, term, Flat.erase, region, bind_assoc]
    apply bind_congr
    intro v
    cases v <;> simp only [diverge_bind]
    case inl x =>
      exact ihl (.skip s _) (extend current x) (agrees_skip s agree _ x)
        _ (fun j edge v => calls j (List.mem_append_left _ edge) v)
    case inr y =>
      exact ihr (.skip s _) (extend current y) (agrees_skip s agree _ y)
        _ (fun j edge v => calls j (List.mem_append_right _ edge) v)

variable {g : FiniteCFG Φ blocks exits n}

private noncomputable abbrev step (g : FiniteCFG Φ blocks exits n) (base : Env α) (p : BlockInput α blocks) :
    Tree Events (Transfer α ⊕ BlockInput α blocks) :=
  region raw (extend base p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)

private theorem row_tree (w : Witness g β R D) (base : Env α) (i : Fin blocks)
    (ranked : ((ranks g).get i).isSome = true) (v : Value α) :
    term raw (extend base v) (erase (compileRankedAt w i ranked).toLetCase.1) =
      (iter (step raw g base) (i, v) >>= fun out => pure (Region.packedExitValue out.1 out.2)) := by
  rw [compileRankedAt]
  rw [body_tree raw (w.block i) (.skip .base (R i)) base (extend base v) (fun _ => rfl)
    (fun j edge => (compileRankedAt w j (Rank.ranked_successor (localTargets g) ranked edge).1).toLetCase)
    (fun p => iter (step raw g base) p >>= fun out => pure (Region.packedExitValue out.1 out.2))
    (fun j edge arg => row_tree w base j (Rank.ranked_successor (localTargets g) ranked edge).1 arg)]
  rw [congrFun (iterate_fixpoint (step raw g base)) (i, v)]
  simp only [bind_assoc, pure_bind]
  exact bind_congr fun p => by cases splitTransfer blocks p <;> simp only [Sum.elim_inl, Sum.elim_inr, pure_bind]
termination_by ((ranks g).get i).getD 0
decreasing_by exact (Rank.ranked_successor (localTargets g) ranked edge).2

theorem compileReachable_tree (w : Witness g β R D) (ranked : entryCheck g = true) (base : Env α) :
    term raw base (erase (compileReachable w ranked).toLetCase.1) =
      (region raw base g.erase >>= fun out => pure (Region.packedExitValue out.1 out.2)) := by
  rw [compileReachable, body_tree raw w.entry .base base base (fun _ => rfl)
    (fun j edge => (compileRankedAt w j (Rank.ranked_of_checkFrom (localTargets g) ranked edge)).toLetCase)
    (fun p => iter (step raw g base) p >>= fun out => pure (Region.packedExitValue out.1 out.2))
    (fun j edge arg => row_tree raw w base j (Rank.ranked_of_checkFrom (localTargets g) ranked edge) arg)]
  simp only [FiniteCFG.erase, region, bind_assoc]
  exact bind_congr fun p => by
    cases splitTransfer blocks p with
    | inl _ => simp only [Sum.elim_inl, pure_bind]
    | inr _ => rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase
