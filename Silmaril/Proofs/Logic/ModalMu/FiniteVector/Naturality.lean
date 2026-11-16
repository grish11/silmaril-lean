module

public import Silmaril.Proofs.Logic.ModalMu.FiniteVector.Compiler

@[expose] public section
namespace Silmaril.Logic.ModalMu.FiniteVector
open CategoryTheory

 theorem System.tail_map {S T : Signature} {k n : Nat} (f : S ⟶ T)
    (s : System S (k+1) n) : (s.map f).tail = s.tail.map f := by
  unfold System.map System.tail
  congr 1
  funext i
  exact (s.body i.succ).renameVars_map f (tailIndex k n)

 theorem headSub_map {S T : Signature} {k n : Nat} (f : S ⟶ T)
    (tail : Fin k → Formula S (n+1)) :
    (fun i => (headSub tail i).map f) = headSub (fun i => (tail i).map f) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp only [headSub, Fin.addCases_left]
    exact Fin.cases rfl (fun _ => rfl) i
  · intro i
    simp only [headSub, Fin.addCases_right]
    rfl

/-- Arbitrary atom/action maps commute syntactically with every compiled output. -/
theorem System.compile_map {S T : Signature} (f : S ⟶ T) (greatest : Bool) :
    ∀ {k n : Nat} (s : System S k n) (i : Fin k),
      (s.compile greatest i).map f = (s.map f).compile greatest i := by
  intro k
  induction k with
  | zero => intro n s i; exact i.elim0
  | succ k ih =>
      intro n s i
      have ht : (fun j => (s.tail.compile greatest j).map f) = (s.map f).tail.compile greatest := by
        rw [s.tail_map]
        funext j
        exact ih _ j
      let head := Vector.binder greatest ((s.body 0).substitute (headSub (s.tail.compile greatest)))
      let head' := Vector.binder greatest (((s.map f).body 0).substitute
        (headSub ((s.map f).tail.compile greatest)))
      have hh : head.map f = head' := by
        rw [Vector.binder_map, Formula.substitute_map, headSub_map, ht]
        rfl
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hh
      · change ((s.tail.compile greatest j).substitute (Fin.cases head Formula.var)).map f =
          (((s.map f).tail.compile greatest j).substitute (Fin.cases head' Formula.var))
        rw [Formula.substitute_map, congrFun ht j]
        apply congrArg (fun σ => ((s.map f).tail.compile greatest j).substitute σ)
        funext l
        exact Fin.cases hh (fun _ => rfl) l

/-- The independently simultaneous semantics obeys the same signature reduct. -/
theorem System.denote_map {S T : Signature} {k n : Nat} (f : S ⟶ T)
    (s : System S k n) (greatest : Bool) (M : Model T) (ρ : Env M.World n) :
    (s.map f).denote greatest M ρ = s.denote greatest (reduct f M) ρ := by
  apply congrArg (fun op => Vector.fixed greatest op)
  apply OrderHom.ext
  funext X i
  exact congrArg (fun op => op (joinEnv ρ X)) ((s.body i).denote_map f M)

/-- Arbitrary captured-variable reindexing, including identifications. -/
theorem System.denote_renameOuter {S : Signature} {k n m : Nat} (s : System S k n)
    (g : Fin n → Fin m) (greatest : Bool) (M : Model S) (ρ : Env M.World m) :
    (s.renameOuter g).denote greatest M ρ = s.denote greatest M (fun i => ρ (g i)) := by
  apply congrArg (fun op => Vector.fixed greatest op)
  apply OrderHom.ext
  funext X i
  change ((s.body i).renameVars _).denote M _ = _
  rw [Formula.denote_renameVars]
  apply congrArg (fun η => (s.body i).denote M η)
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp [joinEnv]
  · intro j
    simp [joinEnv]

/-- Captured-variable reindexing commutes semantically with compilation. -/
theorem System.compile_renameOuter {S : Signature} {k n m : Nat} (s : System S k n)
    (g : Fin n → Fin m) (greatest : Bool) (M : Model S) (ρ : Env M.World m) :
    (fun i => ((s.renameOuter g).compile greatest i).denote M ρ) =
      fun i => (s.compile greatest i).denote M (fun j => ρ (g j)) := by
  rw [System.compile_correct, System.compile_correct, System.denote_renameOuter]

end Silmaril.Logic.ModalMu.FiniteVector
