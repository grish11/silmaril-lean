module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {vars : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {guard : Expr P vars .bool}
variable {body : Stmt P false vars vars} {store : Tuple m.Value vars} {k : Nat}

private theorem checkedGuard (ok : checkWhilePrefix m guard body k store = true) :
    ∃ b : Bool, guard.eval m store = some ⟨b⟩ := by
  have defined : (guard.eval m store).isSome = true := by
    cases k with
    | zero => exact ok
    | succ k => exact (Bool.and_eq_true_iff.mp ok).1
  cases h : guard.eval m store with
  | none => simp [h] at defined
  | some flag => exact ⟨flag.down, rfl⟩

private theorem checkedStep (ok : checkWhilePrefix m guard body (k + 1) store = true) :
    ∃ next, Exec m body.enableWhile store (some next) ∧
      checkWhilePrefix m guard body k next = true := by
  have rest := (Bool.and_eq_true_iff.mp ok).2
  cases h : body.runLoopFree m store with
  | none => simp [h] at rest
  | some next =>
    exact ⟨next, h ▸ body.runLoopFree_enableWhile store, by simpa only [h] using rest⟩

theorem checkedTrace (guard : Expr P vars .bool) (body : Stmt P false vars vars)
    (ret : Port vars t) (neg : P [.bool] .bool) (m : Interpretation.{u,v,w} P) (env : Tuple m.Value vars)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {val : (translate (whileProgram guard body.enableWhile ret) neg).Valuation m}
    (solves : (translate (whileProgram guard body.enableWhile ret) neg).Solves m env val)
    (i : Index (program (whileProgram guard body.enableWhile ret) neg).nodes.length)
    {count : Nat} (first : readWhilePass guard body.enableWhile ret neg m val i = some ⟨count⟩)
    (checked : checkWhilePrefix m guard body count env = true) {value : m.Value t}
    (defined : (translate (whileProgram guard body.enableWhile ret) neg).observe m val i =
      .cons (some value) .nil) :
    ∃ final, WhileTrace m guard body.enableWhile count env final ∧ final.get ret = value := by
  obtain ⟨count', final, trace, result, pass⟩ :=
    whileTraceOfDefinedWith guard body.enableWhile ret neg m env negSem
      (Ready := fun k store => checkWhilePrefix m guard body k store = true)
      checkedGuard (fun h _ => checkedStep h) solves i
      (fun _ pass => by cases first.symm.trans pass; exact checked) defined
  cases first.symm.trans pass
  exact ⟨final, trace, result⟩

end Silmaril.SSA.PEG.Simple.Structured.Proofs
