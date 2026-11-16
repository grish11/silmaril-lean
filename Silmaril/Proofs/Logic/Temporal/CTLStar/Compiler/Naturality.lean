module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.Compiler.Language

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.Compiler
open CategoryTheory

mutual
/-- Actual emitted scalar syntax commutes with arbitrary source atom maps. -/
theorem compileState_map {S T : CTLStar.Signature} (p : StateFormula S) (f : S ⟶ T) :
    (compileState p).map (toMuMap f) = compileState (p.map f) := by
  cases p with
  | atom a => rfl
  | bot => rfl
  | neg p =>
      change (compileState p).dual.map (toMuMap f) = (compileState (p.map f)).dual
      rw [← ModalMu.Formula.dual_map, compileState_map p f]
  | conj p q =>
      change ModalMu.Formula.conj ((compileState p).map (toMuMap f))
        ((compileState q).map (toMuMap f)) =
          .conj (compileState (p.map f)) (compileState (q.map f))
      rw [compileState_map p f, compileState_map q f]
  | existsPath p =>
      change (ModalMu.Formula.replaceAtoms (S := ⟨Closed S, Unit⟩) (T := toMuSig S)
        id id (MaximalPath.formula (compilePathNNF false p) ())).map (toMuMap f) =
          ModalMu.Formula.replaceAtoms (S := ⟨Closed T, Unit⟩) (T := toMuSig T)
            id id (MaximalPath.formula (compilePathNNF false (p.map f)) ())
      let g : (⟨Closed S, Unit⟩ : ModalMu.Signature) ⟶ ⟨Closed T, Unit⟩ :=
        ⟨fun r => r.map (toMuMap f), id⟩
      have hp : (compilePathNNF false p).map (fun r => r.map (toMuMap f)) =
          compilePathNNF false (p.map f) := compilePathNNF_map p f false
      have hm : (MaximalPath.formula (compilePathNNF false p) ()).map g =
          MaximalPath.formula ((compilePathNNF false p).map g.atom) (g.action ()) :=
        MaximalPath.formula_map g (compilePathNNF false p) ()
      rw [ModalMu.Formula.replaceAtoms_map, ← hp, ← hm, ModalMu.Formula.map_replaceAtoms]
      rfl

/-- Fused NNF syntax maps its already compiled closed-formula atoms. -/
theorem compilePathNNF_map {S T : CTLStar.Signature} (p : PathFormula S)
    (f : S ⟶ T) (b : Bool) :
    (compilePathNNF b p).map (fun r => r.map (toMuMap f)) = compilePathNNF b (p.map f) := by
  cases p with
  | state p =>
      have hp := compileState_map p f
      cases b <;> simp only [compilePathNNF, PathFormula.map, NNF.Formula.map, hp]
  | neg p =>
      have hp := compilePathNNF_map p f
      cases b <;> simp only [compilePathNNF, PathFormula.map, hp]
  | conj p q =>
      have hp := compilePathNNF_map p f
      have hq := compilePathNNF_map q f
      cases b <;> simp only [compilePathNNF, PathFormula.map, NNF.Formula.map, hp, hq]
  | next p =>
      have hp := compilePathNNF_map p f
      cases b <;> simp only [compilePathNNF, PathFormula.map, NNF.Formula.map, hp]
  | «until» p q =>
      have hp := compilePathNNF_map p f
      have hq := compilePathNNF_map q f
      cases b <;> simp only [compilePathNNF, PathFormula.map, NNF.Formula.map, hp, hq]
end

end Silmaril.Logic.Temporal.CTLStar.Compiler
