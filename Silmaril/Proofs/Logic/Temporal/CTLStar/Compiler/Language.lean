module

public import Silmaril.Logic.Temporal.CTLStar.Compiler.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.Compiler

/-- The fused helper commutes with existing endpoint-aware normalization as
actual syntax. Its definition itself recurses on original path children. -/
theorem compilePathNNF_eq {S : CTLStar.Signature} (p : PathFormula S) (b : Bool) :
    compilePathNNF b p = (NNF.normalize b p).map compileState := by
  cases p with
  | state p => cases b <;> rfl
  | neg p => cases b <;> exact compilePathNNF_eq p _
  | conj p q =>
      have hp := compilePathNNF_eq p
      have hq := compilePathNNF_eq q
      cases b <;> simp only [compilePathNNF, NNF.normalize, NNF.Formula.map, hp, hq]
  | next p =>
      have hp := compilePathNNF_eq p
      cases b <;> simp only [compilePathNNF, NNF.normalize, NNF.Formula.map, hp]
  | «until» p q =>
      have hp := compilePathNNF_eq p
      have hq := compilePathNNF_eq q
      cases b <;> simp only [compilePathNNF, NNF.normalize, NNF.Formula.map, hp, hq]

/-- Generic closed-formula leaf substitution on the unchanged source frame.
Keeping this composition independent of recursive compiler terms makes the
world and atom interpretation explicit before mutual semantic induction. -/
theorem replace_path_correct {S : CTLStar.Signature} (p : NNF.Formula (Closed S))
    (M : CTLStar.Model S) (ρ : ModalMu.Env M.toModal.World 0) (w : M.toModal.World) :
    w ∈ (ModalMu.Formula.replaceAtoms (S := ⟨Closed S, Unit⟩) (T := toMuSig S)
      id id (MaximalPath.formula p ())).denote (encodeModel M) ρ ↔
      ∃ path : CTLStar.Path M.toModal.accessible, path.state 0 = w ∧
        p.Holds path.last
          (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) 0 := by
  rw [ModalMu.Formula.denote_replaceAtoms]
  exact MaximalPath.formula_correct (S := ⟨Closed S, Unit⟩) p ()
    (ModalMu.atomReduct (S := ⟨Closed S, Unit⟩) (T := toMuSig S) id id (encodeModel M)) ρ w

mutual
/-- Full source state semantics on the original worlds and every closed
external environment. Mutual recursion follows the source grammar. -/
theorem compileState_correct {S : CTLStar.Signature} (p : StateFormula S)
    (M : CTLStar.Model S) (ρ : ModalMu.Env M.toModal.World 0) (w : M.toModal.World) :
    w ∈ (compileState p).denote (encodeModel M) ρ ↔ p.Holds M w := by
  classical
  cases p with
  | atom a => rfl
  | bot => rfl
  | neg p =>
      change w ∈ (compileState p).dual.denote (encodeModel M) ρ ↔ ¬ p.Holds M w
      rw [UniversalPath.closed_dual_correct]
      exact not_congr (compileState_correct p M ρ w)
  | conj p q =>
      change (w ∈ (compileState p).denote (encodeModel M) ρ ∧
        w ∈ (compileState q).denote (encodeModel M) ρ) ↔ p.Holds M w ∧ q.Holds M w
      exact and_congr (compileState_correct p M ρ w) (compileState_correct q M ρ w)
  | existsPath p =>
      change w ∈ (ModalMu.Formula.replaceAtoms
        (S := ⟨Closed S, Unit⟩) (T := toMuSig S) id id
        (MaximalPath.formula (S := ⟨Closed S, Unit⟩)
          (compilePathNNF false p) ())).denote (encodeModel M) ρ ↔ _
      refine (replace_path_correct (compilePathNNF false p) M ρ w).trans ?_
      apply exists_congr
      intro path
      apply and_congr_right
      intro _
      exact compilePathNNF_correct p M path false 0

/-- Fused path normalization has both polarities, including finite endpoints.
Compiled closed-formula atoms are read at the same actual original path world. -/
theorem compilePathNNF_correct {S : CTLStar.Signature} (p : PathFormula S)
    (M : CTLStar.Model S) (path : CTLStar.Path M.toModal.accessible) (b : Bool) (i : Nat) :
    (compilePathNNF b p).Holds path.last
      (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
      if b then ¬ p.Holds M path i else p.Holds M path i := by
  classical
  cases p with
  | state p =>
      have hp : path.state i ∈ (compileState p).denote (encodeModel M) ModalMu.emptyEnv ↔
        p.Holds M (path.state i) := compileState_correct p M ModalMu.emptyEnv (path.state i)
      cases b
      · exact hp
      · exact not_congr hp
  | neg p =>
      have hp (b : Bool) (i : Nat) :
          (compilePathNNF b p).Holds path.last
            (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
          if b then ¬ p.Holds M path i else p.Holds M path i :=
        compilePathNNF_correct p M path b i
      cases b <;> simp [compilePathNNF, PathFormula.Holds, hp]
  | conj p q =>
      change (compilePathNNF b (.conj p q)).Holds path.last
        (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
        (if b then ¬ (p.Holds M path i ∧ q.Holds M path i)
          else p.Holds M path i ∧ q.Holds M path i)
      have hp (b : Bool) (i : Nat) :
          (compilePathNNF b p).Holds path.last
            (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
          if b then ¬ p.Holds M path i else p.Holds M path i :=
        compilePathNNF_correct p M path b i
      have hq (b : Bool) (i : Nat) :
          (compilePathNNF b q).Holds path.last
            (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
          if b then ¬ q.Holds M path i else q.Holds M path i :=
        compilePathNNF_correct q M path b i
      cases b <;> simp [compilePathNNF, NNF.Formula.Holds, hp, hq, or_iff_not_imp_left]
  | next p =>
      have hp (b : Bool) (i : Nat) :
          (compilePathNNF b p).Holds path.last
            (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
          if b then ¬ p.Holds M path i else p.Holds M path i :=
        compilePathNNF_correct p M path b i
      cases b <;> simp [compilePathNNF, NNF.Formula.Holds, PathFormula.Holds, hp, Path.Valid]
  | «until» p q =>
      have hp (b : Bool) (i : Nat) :
          (compilePathNNF b p).Holds path.last
            (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
          if b then ¬ p.Holds M path i else p.Holds M path i :=
        compilePathNNF_correct p M path b i
      have hq (b : Bool) (i : Nat) :
          (compilePathNNF b q).Holds path.last
            (fun t r => path.state t ∈ r.denote (encodeModel M) ModalMu.emptyEnv) i ↔
          if b then ¬ q.Holds M path i else q.Holds M path i :=
        compilePathNNF_correct q M path b i
      cases b <;> simp [compilePathNNF, NNF.Formula.Holds, PathFormula.Holds, hp, hq,
        Path.Valid, or_iff_not_imp_left]
end

end Silmaril.Logic.Temporal.CTLStar.Compiler
