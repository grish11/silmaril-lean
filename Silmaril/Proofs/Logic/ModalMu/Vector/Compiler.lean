module

public import Silmaril.Proofs.Logic.ModalMu.Vector.Bekic

@[expose] public section
namespace Silmaril.Logic.ModalMu.Vector
open CategoryTheory

 theorem binder_denote {S : Signature} {n : Nat} (M : Model S) (greatest : Bool)
    (p : Formula S (n+1)) (ρ : Env M.World n) :
    (binder greatest p).denote M ρ = fixed greatest ((p.denote M).comp (insert ρ)) := by
  cases greatest <;> rfl

theorem System.secondParam_denote {S : Signature} {n : Nat} (s : System S n) (greatest : Bool)
    (M : Model S) (ρ : Env M.World n) (X : Set M.World) :
    (s.secondParam greatest).denote M (extend ρ X) =
      secondSolutions greatest (s.operator M ρ) X := by
  rw [System.secondParam, binder_denote]
  apply congrArg (fun f => fixed greatest f)
  apply OrderHom.ext
  funext Y
  change (s.second.renameVars (swap n)).denote M (extend (extend ρ X) Y) = _
  rw [Formula.denote_renameVars]
  apply congrArg (fun η => s.second.denote M η)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact Fin.cases rfl (fun _ => rfl) j

theorem System.firstScalar_denote {S : Signature} {n : Nat} (s : System S n) (greatest : Bool)
    (M : Model S) (ρ : Env M.World n) :
    (s.firstScalar greatest).denote M ρ = fixed greatest (reduced greatest (s.operator M ρ)) := by
  rw [System.firstScalar, binder_denote]
  apply congrArg (fun f => fixed greatest f)
  apply OrderHom.ext
  funext X
  change (s.first.substitute _).denote M (extend ρ X) = _
  rw [Formula.denote_substitute]
  change s.first.denote M _ = s.first.denote M _
  apply congrArg (fun η => s.first.denote M η)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun _ => rfl) j
    exact s.secondParam_denote greatest M ρ X

theorem System.secondScalar_denote {S : Signature} {n : Nat} (s : System S n) (greatest : Bool)
    (M : Model S) (ρ : Env M.World n) :
    (s.secondScalar greatest).denote M ρ =
      secondSolutions greatest (s.operator M ρ) (fixed greatest (reduced greatest (s.operator M ρ))) := by
  rw [System.secondScalar, Formula.denote_substitute]
  have h : (fun i : Fin (n+1) => (Fin.cases (motive := fun _ => Formula S n) (s.firstScalar greatest) (fun i => Formula.var i) i).denote M ρ) =
      extend ρ ((s.firstScalar greatest).denote M ρ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [h, s.secondParam_denote, s.firstScalar_denote]

/-- Both actual scalar formula denotations equal the independent simultaneous
product fixed point, for either uniform μ or ν and every captured valuation. -/
theorem System.compile_correct {S : Signature} {n : Nat} (s : System S n) (greatest : Bool)
    (M : Model S) (ρ : Env M.World n) :
    ((s.firstScalar greatest).denote M ρ, (s.secondScalar greatest).denote M ρ) =
      s.denote greatest M ρ := by
  rw [s.firstScalar_denote, s.secondScalar_denote]
  exact (bekic greatest (s.operator M ρ)).symm

theorem binder_map {S T : Signature} {n : Nat} (f : S ⟶ T) (greatest : Bool)
    (p : Formula S (n+1)) : (binder greatest p).map f = binder greatest (p.map f) := by
  cases greatest <;> rfl

theorem System.secondParam_map {S T : Signature} {n : Nat} (f : S ⟶ T)
    (s : System S n) (greatest : Bool) :
    (s.secondParam greatest).map f = (s.map f).secondParam greatest := by
  rw [System.secondParam, binder_map]
  exact congrArg (binder greatest) (s.second.renameVars_map f (swap n)).symm

theorem System.firstScalar_map {S T : Signature} {n : Nat} (f : S ⟶ T)
    (s : System S n) (greatest : Bool) :
    (s.firstScalar greatest).map f = (s.map f).firstScalar greatest := by
  rw [System.firstScalar, binder_map, Formula.substitute_map]
  apply congrArg (fun σ => binder greatest ((s.first.map f).substitute σ))
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact Fin.cases (s.secondParam_map f greatest) (fun _ => rfl) j

theorem System.secondScalar_map {S T : Signature} {n : Nat} (f : S ⟶ T)
    (s : System S n) (greatest : Bool) :
    (s.secondScalar greatest).map f = (s.map f).secondScalar greatest := by
  rw [System.secondScalar, Formula.substitute_map, s.secondParam_map]
  apply congrArg (fun σ => ((s.map f).secondParam greatest).substitute σ)
  funext i
  exact Fin.cases (s.firstScalar_map f greatest) (fun _ => rfl) i

/-- Source product semantics respects actual atom/action signature reducts. -/
theorem System.denote_map {S T : Signature} {n : Nat} (f : S ⟶ T)
    (s : System S n) (greatest : Bool) (M : Model T) (ρ : Env M.World n) :
    (s.map f).denote greatest M ρ = s.denote greatest (reduct f M) ρ := by
  apply congrArg (fun op => fixed greatest op)
  apply OrderHom.ext
  funext P
  change ((s.first.map f).denote M _, (s.second.map f).denote M _) = _
  rw [Formula.denote_map, Formula.denote_map]
  rfl

/-- Arbitrary captured-variable reindexing, including identifications, commutes
with the independently simultaneous source semantics. -/
theorem System.denote_renameOuter {S : Signature} {n m : Nat} (s : System S n)
    (g : Fin n → Fin m) (greatest : Bool) (M : Model S) (ρ : Env M.World m) :
    (s.renameOuter g).denote greatest M ρ = s.denote greatest M (fun i => ρ (g i)) := by
  have env (P : Set M.World × Set M.World) :
      (fun i => pairEnv ρ P (liftVars (liftVars g) i)) = pairEnv (fun i => ρ (g i)) P := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  apply congrArg (fun op => fixed greatest op)
  apply OrderHom.ext
  funext P
  change ((s.first.renameVars _).denote M _, (s.second.renameVars _).denote M _) = _
  rw [Formula.denote_renameVars, Formula.denote_renameVars, env]
  rfl

/-- The actual compiled outputs preserve arbitrary captured-variable reindexing
semantically; signature-map naturality above is a syntactic equality. -/
theorem System.compile_renameOuter {S : Signature} {n m : Nat} (s : System S n)
    (g : Fin n → Fin m) (greatest : Bool) (M : Model S) (ρ : Env M.World m) :
    (((s.renameOuter g).firstScalar greatest).denote M ρ,
      ((s.renameOuter g).secondScalar greatest).denote M ρ) =
    ((s.firstScalar greatest).denote M (fun i => ρ (g i)),
      (s.secondScalar greatest).denote M (fun i => ρ (g i))) := by
  rw [System.compile_correct, System.compile_correct, System.denote_renameOuter]

end Silmaril.Logic.ModalMu.Vector
