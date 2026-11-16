module

public import Silmaril.Logic.Kore.Operational.Defs
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.Kore.Operational
open Silmaril.Logic Silmaril.Logic.Kore.Operational

private theorem app_denote {S : Type} {A : Algebraic.ManySorted.Signature S}
    (M : Matching.FirstOrder.Model A) {k : Nat} {Γ : Fin k → S} {n : Nat}
    {inputs : Fin n → S} {output : S} (op : A.operations n inputs output)
    (args : (i : Fin n) → Matching.FirstOrder.Pattern A Γ (inputs i))
    (v : (i : Fin k) → M.carrier (Γ i)) (values : (i : Fin n) → M.carrier (inputs i))
    (h : ∀ i, M.denote v (args i) = {values i}) :
    M.denote v (.app op args) = M.operation op values := by
  ext result
  constructor
  · rintro ⟨xs, hx, hr⟩
    have he : xs = values := by
      funext i
      have hi := hx i
      rw [h i] at hi
      exact hi
    simpa only [he] using hr
  · intro hr
    exact ⟨values, fun i => by rw [h i]; rfl, hr⟩

private theorem token_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (s : String) :
    (model R).denote v (tokenPattern s) = {s} := by
  exact app_denote (model R) (.token s) (fun i => i.elim0) v (fun i => i.elim0) (fun i => i.elim0)

private theorem item_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (s : String) :
    (model R).denote v (itemPattern s) = {s} := by
  exact app_denote (model R) .injection (fun _ => tokenPattern s) v (fun _ => s)
    (fun _ => token_denote R v s)

private theorem code_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (s : String) :
    (model R).denote v (codePattern s) = {s :: v 0} := by
  let values : (i : Fin 2) → Carrier (if i = 0 then .item else .code) :=
    fun i => if h : i = 0 then by subst i; exact s else by
      have hi : i = 1 := by omega
      subst i; exact v 0
  unfold codePattern
  change _ = (model R).operation .sequence values
  apply app_denote (model R) .sequence _ v values
  intro i
  fin_cases i
  · exact item_denote R v s
  · rfl

private theorem cell_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (s : String) :
    (model R).denote v (cellPattern s) = {s :: v 0} := by
  exact app_denote (model R) .kcell (fun _ => codePattern s) v (fun _ => s :: v 0)
    (fun _ => code_denote R v s)

theorem compile_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (p : ConfigPattern) :
    (model R).denote v p.compile = {⟨p.state :: v 0, v 1⟩} := by
  let values : (i : Fin 2) → Carrier (if i = 0 then .cell else .counter) :=
    fun i => if h : i = 0 then by subst i; exact p.state :: v 0 else by
      have hi : i = 1 := by omega
      subst i; exact v 1
  unfold ConfigPattern.compile
  change _ = (model R).operation .topcell values
  apply app_denote (model R) .topcell _ v values
  intro i
  fin_cases i
  · exact cell_denote R v p.state
  · rfl

/-- Exact native successor set, not an atom carrying an external proposition. -/
theorem next_compile_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (p : ConfigPattern) :
    (model R).denote v (.app .step (fun _ => p.compile)) =
      nextDenote R {⟨p.state :: v 0, v 1⟩} := by
  calc
    _ = {c | R c ⟨p.state :: v 0, v 1⟩} :=
      app_denote (model R) .step (fun _ => p.compile) v
        (fun _ => ⟨p.state :: v 0, v 1⟩) (fun _ => compile_denote R v p)
    _ = _ := by ext c; simp [nextDenote]

end Silmaril.Proofs.Logic.Kore.Operational
