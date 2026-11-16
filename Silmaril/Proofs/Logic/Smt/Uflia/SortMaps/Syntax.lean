module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Hom
open CategoryTheory Silmaril.Logic.Algebraic
variable {A B C : Signature}

private theorem operation_heq (f : A ⟶ B) {n : Nat}
    {ss tt : Fin n → SortCode A.users} {s t : SortCode A.users}
    (hss : ss = tt) (hs : s = t)
    (op : Operation A.symbols n ss s) (op' : Operation A.symbols n tt t)
    (hop : HEq op op') : HEq (operation f op) (operation f op') := by
  cases hss
  cases hs
  cases eq_of_heq hop
  rfl

private theorem ite_heq (f : A ⟶ B) (s : SortCode A.users) :
    HEq (operation f (.ite s)) (Operation.ite (A := B.symbols) (f.sorts s)) := by
  have profiles : f.sorts ∘ Fin.cases .bool (fun _ : Fin 2 => s) =
      Fin.cases .bool (fun _ : Fin 2 => f.sorts s) := by
    funext i
    exact Fin.cases f.bool (fun _ => rfl) i
  have shifted : operation f (.ite s) =
      profiles.symm ▸ (Operation.ite (A := B.symbols) (f.sorts s)) := by
    cases s <;> rfl
  rw [shifted]
  exact eqRec_heq (φ := fun ss : Fin 3 → SortCode B.users =>
    Operation B.symbols 3 ss (f.sorts s)) profiles.symm (.ite (f.sorts s))

theorem operation_id {n inputs output} (op : Operation A.symbols n inputs output) :
    operation (𝟙 A) op = op := by
  cases op <;> rfl

theorem operation_comp (f : A ⟶ B) (g : B ⟶ C) {n inputs output}
    (op : Operation A.symbols n inputs output) :
    operation (f ≫ g) op = operation g (operation f op) := by
  cases op with
  | uf symbol => rfl
  | boolean b =>
      have hf : HEq (operation f (.boolean b)) (Operation.boolean (A := B.symbols) b) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (sorts_empty f) f.bool (operation f (.boolean b)) (.boolean b) hf
      have hg : HEq (operation g (.boolean b)) (Operation.boolean (A := C.symbols) b) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.boolean b)) (Operation.boolean (A := C.symbols) b) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | integer b =>
      have hf : HEq (operation f (.integer b)) (Operation.integer (A := B.symbols) b) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (sorts_empty f) f.int (operation f (.integer b)) (.integer b) hf
      have hg : HEq (operation g (.integer b)) (Operation.integer (A := C.symbols) b) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.integer b)) (Operation.integer (A := C.symbols) b) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | add =>
      have hf : HEq (operation f (.add)) (Operation.add (A := B.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.int)) f.int (operation f (.add)) (.add) hf
      have hg : HEq (operation g (.add)) (Operation.add (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.add)) (Operation.add (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | sub =>
      have hf : HEq (operation f (.sub)) (Operation.sub (A := B.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.int)) f.int (operation f (.sub)) (.sub) hf
      have hg : HEq (operation g (.sub)) (Operation.sub (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.sub)) (Operation.sub (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | scale c =>
      have hf : HEq (operation f (.scale c)) (Operation.scale (A := B.symbols) c) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.int)) f.int (operation f (.scale c)) (.scale c) hf
      have hg : HEq (operation g (.scale c)) (Operation.scale (A := C.symbols) c) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.scale c)) (Operation.scale (A := C.symbols) c) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | le =>
      have hf : HEq (operation f (.le)) (Operation.le (A := B.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.int)) f.bool (operation f (.le)) (.le) hf
      have hg : HEq (operation g (.le)) (Operation.le (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.le)) (Operation.le (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | lt =>
      have hf : HEq (operation f (.lt)) (Operation.lt (A := B.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.int)) f.bool (operation f (.lt)) (.lt) hf
      have hg : HEq (operation g (.lt)) (Operation.lt (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.lt)) (Operation.lt (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | not =>
      have hf : HEq (operation f (.not)) (Operation.not (A := B.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.bool)) f.bool (operation f (.not)) (.not) hf
      have hg : HEq (operation g (.not)) (Operation.not (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.not)) (Operation.not (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | and =>
      have hf : HEq (operation f (.and)) (Operation.and (A := B.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.bool)) f.bool (operation f (.and)) (.and) hf
      have hg : HEq (operation g (.and)) (Operation.and (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.and)) (Operation.and (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | or =>
      have hf : HEq (operation f (.or)) (Operation.or (A := B.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (funext (fun _ => f.bool)) f.bool (operation f (.or)) (.or) hf
      have hg : HEq (operation g (.or)) (Operation.or (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.or)) (Operation.or (A := C.symbols)) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | eq s =>
      have hf : HEq (operation f (.eq s)) (Operation.eq (A := B.symbols) (f.sorts s)) := by
        unfold operation
        exact cast_heq _ _
      have hfg := operation_heq g (rfl) f.bool (operation f (.eq s)) (.eq (f.sorts s)) hf
      have hg : HEq (operation g (.eq (f.sorts s))) (Operation.eq (A := C.symbols) (g.sorts (f.sorts s))) := by
        unfold operation
        exact cast_heq _ _
      have hc : HEq (operation (f ≫ g) (.eq s)) (Operation.eq (A := C.symbols) (g.sorts (f.sorts s))) := by
        unfold operation
        exact cast_heq _ _
      exact eq_of_heq (hc.trans (hfg.trans hg).symm)
  | ite _ =>
      have profiles : f.sorts ∘ Fin.cases .bool (fun _ : Fin 2 => output) =
          Fin.cases .bool (fun _ : Fin 2 => f.sorts output) := by
        funext i
        exact Fin.cases f.bool (fun _ => rfl) i
      have hf := ite_heq f output
      have hfg := operation_heq g profiles rfl (operation f (.ite output)) (.ite (f.sorts output)) hf
      exact eq_of_heq ((ite_heq (f ≫ g) output).trans
        ((hfg.trans (ite_heq g (f.sorts output))).symm))

private theorem term_heq (f : A ⟶ B) {k : Nat}
    {Γ Δ : Fin k → SortCode A.users} {s t : SortCode A.users}
    (hΓ : Γ = Δ) (hs : s = t)
    (p : ManySorted.Term A.symbols.expanded Γ s)
    (q : ManySorted.Term A.symbols.expanded Δ t) (hp : HEq p q) :
    HEq (term f p) (term f q) := by
  cases hΓ
  cases hs
  cases eq_of_heq hp
  rfl

theorem term_id {k : Nat} {Γ : Fin k → SortCode A.users} {s : SortCode A.users}
    (p : ManySorted.Term A.symbols.expanded Γ s) : term (𝟙 A) p = p := by
  induction p with
  | var i => rfl
  | app op args ih =>
      simp only [term, operation_id]
      exact congrArg (ManySorted.Term.app op) (funext ih)

theorem term_comp (f : A ⟶ B) (g : B ⟶ C) {k : Nat}
    {Γ : Fin k → SortCode A.users} {s : SortCode A.users}
    (p : ManySorted.Term A.symbols.expanded Γ s) :
    term (f ≫ g) p = term g (term f p) := by
  induction p with
  | var i => rfl
  | app op args ih =>
      simp only [term, operation_comp]
      exact congrArg (ManySorted.Term.app (operation g (operation f op))) (funext ih)

theorem formula_id (p : Formula A.symbols) : formula (𝟙 A) p = p :=
  eq_of_heq ((formula_heq (𝟙 A) p).trans (heq_of_eq (term_id p)))

theorem formula_comp (f : A ⟶ B) (g : B ⟶ C) (p : Formula A.symbols) :
    formula (f ≫ g) p = formula g (formula f p) := by
  have inner := term_heq g (sorts_empty f).symm f.bool.symm
    (formula f p) (term f p) (formula_heq f p)
  exact eq_of_heq ((formula_heq (f ≫ g) p).trans ((heq_of_eq (term_comp f g p)).trans
    (((formula_heq g (formula f p)).trans inner).symm)))

end Silmaril.Logic.Smt.Uflia.SortMaps.Hom
