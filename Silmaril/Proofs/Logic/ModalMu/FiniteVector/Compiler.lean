module

public import Silmaril.Proofs.Logic.ModalMu.FiniteVector.FixedPoints

@[expose] public section
namespace Silmaril.Logic.ModalMu.FiniteVector
open CategoryTheory

/-- The renamed tail has exactly the parametric source semantics. -/
theorem System.tail_operator {S : Signature} {k n : Nat} (s : System S (k+1) n)
    (M : Model S) (ρ : Env M.World n) (X : Set M.World) (Y : Env M.World k) :
    s.tail.operator M (extend ρ X) Y = fun i => s.operator M ρ (Fin.cases X Y) i.succ := by
  funext i
  change ((s.body i.succ).renameVars _).denote M _ = _
  rw [Formula.denote_renameVars]
  apply congrArg (fun η => (s.body i.succ).denote M η)
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [tailIndex, joinEnv, extend]
    · simp [tailIndex, joinEnv]
  · intro j
    simp [tailIndex, joinEnv, extend]

/-- Both the base frame and captured outer valuation are unrestricted. -/
theorem System.compile_correct {S : Signature} (greatest : Bool) :
    ∀ {k n : Nat} (s : System S k n) (M : Model S) (ρ : Env M.World n),
      (fun i => (s.compile greatest i).denote M ρ) = s.denote greatest M ρ := by
  intro k
  induction k with
  | zero => intro n s M ρ; funext i; exact i.elim0
  | succ k ih =>
      intro n s M ρ
      let e := splitEnv M.World k
      let f := s.operator M ρ
      let g := (orderMap e).comp (f.comp (orderMap e.symm))
      let tail := s.tail.compile greatest
      have tail_sem (X : Set M.World) :
          (fun i => (tail i).denote M (extend ρ X)) = Vector.secondSolutions greatest g X := by
        rw [ih]
        apply congrArg (fun op => Vector.fixed greatest op)
        apply OrderHom.ext
        funext Y
        exact s.tail_operator M ρ X Y
      let head := Vector.binder greatest ((s.body 0).substitute (headSub tail))
      have head_sem : head.denote M ρ = Vector.fixed greatest (Vector.reduced greatest g) := by
        rw [Vector.binder_denote]
        apply congrArg (fun op => Vector.fixed greatest op)
        apply OrderHom.ext
        funext X
        change ((s.body 0).substitute _).denote M (extend ρ X) = _
        rw [Formula.denote_substitute]
        change (s.body 0).denote M _ = (s.body 0).denote M _
        apply congrArg (fun η => (s.body 0).denote M η)
        funext j
        refine Fin.addCases ?_ ?_ j
        · intro j
          refine Fin.cases ?_ (fun i => ?_) j
          · simp [headSub, joinEnv, Formula.denote, orderMap, e, splitEnv]
            rfl
          · simpa [headSub, joinEnv, orderMap, e, splitEnv] using congrFun (tail_sem X) i
        · intro j
          simp [headSub, joinEnv, Formula.denote]
          rfl
      have output_sem : e (fun i => (s.compile greatest i).denote M ρ) =
          (Vector.fixed greatest (Vector.reduced greatest g),
            Vector.secondSolutions greatest g (Vector.fixed greatest (Vector.reduced greatest g))) := by
        apply Prod.ext
        · exact head_sem
        · change (fun i => ((tail i).substitute (Fin.cases head Formula.var)).denote M ρ) = _
          have inst : (fun i => ((tail i).substitute (Fin.cases head Formula.var)).denote M ρ) =
              fun i => (tail i).denote M (extend ρ (head.denote M ρ)) := by
            funext i
            rw [Formula.denote_substitute]
            apply congrArg (fun η => (tail i).denote M η)
            funext j
            exact Fin.cases rfl (fun _ => rfl) j
          rw [inst, tail_sem, head_sem]
      apply e.injective
      rw [output_sem, ← Vector.bekic]
      exact (fixed_conjugate e f greatest).symm

end Silmaril.Logic.ModalMu.FiniteVector
