module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Hom
open CategoryTheory Silmaril.Logic.Algebraic
variable {A B C : Signature}

theorem sorts_empty (f : A ⟶ B) :
    f.sorts ∘ (Fin.elim0 : Fin 0 → SortCode A.users) = Fin.elim0 := by
  funext i
  exact i.elim0

theorem sorts_cons (f : A ⟶ B) {n : Nat} (s : SortCode A.users)
    (ss : Fin n → SortCode A.users) :
    f.sorts ∘ Fin.cases s ss = Fin.cases (f.sorts s) (f.sorts ∘ ss) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Built-ins retain their meanings while their argument/result types move. -/
def operation (f : A ⟶ B) : {n : Nat} → {inputs : Fin n → SortCode A.users} →
    {output : SortCode A.users} → Operation A.symbols n inputs output →
    Operation B.symbols n (f.sorts ∘ inputs) (f.sorts output)
  | _, _, _, .uf symbol => .uf (f.operations symbol)
  | _, _, _, .boolean b => by simpa only [f.bool, sorts_empty] using (Operation.boolean (A := B.symbols) b)
  | _, _, _, .integer i => by simpa only [f.int, sorts_empty] using (Operation.integer (A := B.symbols) i)
  | _, _, _, .add => by simpa only [Function.comp_def, f.int] using (Operation.add (A := B.symbols))
  | _, _, _, .sub => by simpa only [Function.comp_def, f.int] using (Operation.sub (A := B.symbols))
  | _, _, _, .scale c => by simpa only [Function.comp_def, f.int] using (Operation.scale (A := B.symbols) c)
  | _, _, _, .le => by simpa only [Function.comp_def, f.int, f.bool] using (Operation.le (A := B.symbols))
  | _, _, _, .lt => by simpa only [Function.comp_def, f.int, f.bool] using (Operation.lt (A := B.symbols))
  | _, _, _, .eq s => by simpa only [Function.comp_def, f.bool] using (Operation.eq (A := B.symbols) (f.sorts s))
  | _, _, _, .not => by simpa only [Function.comp_def, f.bool] using (Operation.not (A := B.symbols))
  | _, _, _, .and => by simpa only [Function.comp_def, f.bool] using (Operation.and (A := B.symbols))
  | _, _, _, .or => by simpa only [Function.comp_def, f.bool] using (Operation.or (A := B.symbols))
  | _, _, _, .ite s => by
      have profiles : f.sorts ∘ Fin.cases .bool (fun _ : Fin 2 => s) =
          Fin.cases .bool (fun _ : Fin 2 => f.sorts s) := by
        funext i
        exact Fin.cases f.bool (fun _ => rfl) i
      exact profiles.symm ▸ (Operation.ite (A := B.symbols) (f.sorts s))

/-- Reindex open ground-core terms, including result and context sorts. -/
def term (f : A ⟶ B) {k : Nat} {Γ : Fin k → SortCode A.users} {s : SortCode A.users} :
    ManySorted.Term A.symbols.expanded Γ s →
      ManySorted.Term B.symbols.expanded (f.sorts ∘ Γ) (f.sorts s)
  | .var i => .var i
  | .app op args => .app (operation f op) (fun i => term f (args i))

/-- The closed Boolean sort is preserved by every signature arrow. -/
def formula (f : A ⟶ B) (p : Formula A.symbols) : Formula B.symbols := by
  have t := term f p
  rw [sorts_empty f, f.bool] at t
  exact t

end Silmaril.Logic.Smt.Uflia.SortMaps.Hom
