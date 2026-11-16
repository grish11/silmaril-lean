module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Transport.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {A B : Signature}

theorem map_substitute {S T : EQ.Signature} (f : S ⟶ T) {k l}
    {Γ : Fin k → S.S} {Δ : Fin l → S.S} (σ : ∀ i, EQ.Term S Δ (Γ i))
    {s} (t : EQ.Term S Γ s) :
    (substitute σ t).map f = substitute (fun i => (σ i).map f) (t.map f) := by
  induction t with
  | var i => rfl
  | app o args ih => exact congrArg (EQ.Term.app (f.ops o)) (funext ih)

theorem map_liftTerm (f : A ⟶ B) {k} {Γ : Fin k → TargetSort} (s : TargetSort)
    {t} (u : TargetTerm A Γ t) :
    (liftTerm (S := (signature A).toSignature) s u).map (signatureMap f).toHom =
      liftTerm (S := (signature B).toSignature) s (u.map (signatureMap f).toHom) := by
  rw [liftTerm,map_substitute]
  rfl

theorem map_liftHeap (f : A ⟶ B) {k} {Γ : Fin k → TargetSort} {s} (u : TargetTerm A Γ s) :
    (liftHeap u).map (signatureMap f).toHom = liftHeap (u.map (signatureMap f).toHom) :=
  map_liftTerm f .heap u

theorem term_map (f : A ⟶ B) {k l} {Γ : Fin l → TargetSort}
    (σ : Fin k → TargetTerm A Γ .value) (t : Term A k) :
    (term σ t).map (signatureMap f).toHom =
      term (fun i => (σ i).map (signatureMap f).toHom) (t.map f) := by
  induction t with
  | var i => rfl
  | app o args ih => exact congrArg (EQ.Term.app (Operation.value (f.operation o))) (funext ih)

theorem recursiveArgs_map (f : A ⟶ B) {n l} {Γ : Fin l → TargetSort}
    (h : TargetTerm A Γ .heap) (args : Fin n → TargetTerm A Γ .value) :
    (fun i => (recursiveArgs h args i).map (signatureMap f).toHom) =
      recursiveArgs (h.map (signatureMap f).toHom) (fun i => (args i).map (signatureMap f).toHom) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem joinFormula_map (f : A ⟶ B) {k} {Γ : Fin k → TargetSort}
    (a b c : TargetTerm A Γ .heap) :
    (joinFormula a b c).map (signatureMap f) = joinFormula (a.map (signatureMap f).toHom)
      (b.map (signatureMap f).toHom) (c.map (signatureMap f).toHom) := by
  change FOL.Formula.rel (Sg := signature B) (Relation.join (A := B)) _ =
    FOL.Formula.rel (Sg := signature B) (Relation.join (A := B)) _
  apply congrArg (FOL.Formula.rel (Sg := signature B) Relation.join)
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  exact Fin.cases rfl (fun _ => rfl) j

theorem ownershipFormula_map (f : A ⟶ B) {k n} {Γ : Fin k → TargetSort}
    (a : A.Atom n) (args : Fin n → TargetTerm A Γ .value) (h : TargetTerm A Γ .heap) :
    (ownershipFormula a args h).map (signatureMap f) = ownershipFormula (f.atom a)
      (fun i => (args i).map (signatureMap f).toHom) (h.map (signatureMap f).toHom) := by
  change FOL.Formula.rel (Sg := signature B) (Relation.atom (f.atom a)) _ =
    FOL.Formula.rel (Sg := signature B) (Relation.atom (f.atom a)) _
  exact congrArg (FOL.Formula.rel (Sg := signature B) (Relation.atom (f.atom a))) (recursiveArgs_map f h args)

theorem assertion_map (f : A ⟶ B) {k} (p : Assertion A k) {l} {Γ : Fin l → TargetSort}
    (σ : Fin k → TargetTerm A Γ .value) (h : TargetTerm A Γ .heap) :
    (assertion p σ h).map (signatureMap f) = assertion (p.map f)
      (fun i => (σ i).map (signatureMap f).toHom) (h.map (signatureMap f).toHom) := by
  induction p generalizing l with
  | eq t u => exact congrArg₂ FOL.Formula.eq (term_map f σ t) (term_map f σ u)
  | atom a args =>
      rw [assertion,ownershipFormula_map]
      simp only [Assertion.map,assertion,term_map]
  | emp =>
      change FOL.Formula.eq (h.map (signatureMap f).toHom) _ = FOL.Formula.eq (h.map (signatureMap f).toHom) _
      congr 2
      change EQ.Term.app (Sg := (signature B).toSignature) (Γ := Γ) (Operation.unit (A := B)) _ =
        EQ.Term.app (Sg := (signature B).toSignature) (Γ := Γ) (Operation.unit (A := B)) _
      congr 1
      funext i
      exact i.elim0
  | neg p ih => exact congrArg FOL.Formula.not (ih σ h)
  | conj p q hp hq => exact congrArg₂ FOL.Formula.and (hp σ h) (hq σ h)
  | sep p q hp hq =>
      simp only [assertion,Assertion.map,existsFormula,forallFormula,FOL.Formula.map,
        joinFormula_map,hp,hq,map_liftHeap]
      rfl
  | wand p q hp hq =>
      simp only [assertion,Assertion.map,forallFormula,impliesFormula,FOL.Formula.map,
        joinFormula_map,hp,hq,map_liftHeap]
      rfl

theorem map_castTerm (f : A ⟶ B) {k} {Γ : Fin k → TargetSort} {s t}
    (e : s = t) (u : TargetTerm A Γ s) :
    (Eq.mp (congrArg (TargetTerm A Γ) e) u).map (signatureMap f).toHom =
      Eq.mp (congrArg (TargetTerm B Γ) e) (u.map (signatureMap f).toHom) := by
  cases e
  rfl

theorem tupleHeap_map (f : A ⟶ B) {l} (n : Nat) (Γ : Fin l → TargetSort) :
    (tupleHeap (A := A) n Γ).map (signatureMap f).toHom = tupleHeap (A := B) n Γ := by
  have he : tupleContext n Γ ((0 : Fin (n+1)).castAdd l) = .heap := by
    simp [tupleContext,pointerHeapTargetSorts]
  exact map_castTerm f he (.var ((0 : Fin (n+1)).castAdd l))

theorem tupleValue_map (f : A ⟶ B) {l} (n : Nat) (Γ : Fin l → TargetSort) (j : Fin n) :
    (tupleValue (A := A) n Γ j).map (signatureMap f).toHom = tupleValue (A := B) n Γ j := by
  have he : tupleContext n Γ (j.succ.castAdd l) = .value := by
    simp [tupleContext,pointerHeapTargetSorts]
  exact map_castTerm f he (.var (j.succ.castAdd l))

theorem tupleAmbientVar_map (f : A ⟶ B) {l} (n : Nat) (Γ : Fin l → TargetSort) (i : Fin l) :
    (tupleAmbientVar (A := A) n Γ i).map (signatureMap f).toHom = tupleAmbientVar (A := B) n Γ i := by
  have he : tupleContext n Γ (Fin.natAdd (n+1) i) = Γ i := by
    simp [tupleContext]
  exact map_castTerm f he (.var (Fin.natAdd (n+1) i))

theorem bodyValues_map (f : A ⟶ B) {k l} {Γ : Fin l → TargetSort} (n : Nat)
    (σ : Fin k → TargetTerm A Γ .value) :
    (fun i => (bodyValues n σ i).map (signatureMap f).toHom) =
      bodyValues n (fun i => (σ i).map (signatureMap f).toHom) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [bodyValues,Fin.addCases_left,tupleValue_map]
    rfl
  · intro j
    simp only [bodyValues,Fin.addCases_right,map_substitute,tupleAmbientVar_map]
    rfl

theorem boundValues_map (f : A ⟶ B) {k l} {Γ : Fin l → TargetSort}
    (σ : Fin k → TargetTerm A Γ .value) :
    (fun i => (boundValues σ i).map (signatureMap f).toHom) =
      boundValues (fun i => (σ i).map (signatureMap f).toHom) := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  exact map_liftTerm f .value (σ j)

theorem compiledArgs_map (f : A ⟶ B) {n k l} {Γ : Fin l → TargetSort}
    (h : TargetTerm A Γ .heap) (σ : Fin k → TargetTerm A Γ .value) (args : Fin n → Term A k) :
    (fun i => (recursiveArgs h (fun j => term σ (args j)) i).map (signatureMap f).toHom) =
      recursiveArgs (h.map (signatureMap f).toHom)
        (fun j => term (fun i => (σ i).map (signatureMap f).toHom) ((args j).map f)) := by
  exact (recursiveArgs_map f h (fun j => term σ (args j))).trans
    (congrArg (recursiveArgs (h.map (signatureMap f).toHom)) (funext fun j => term_map f σ (args j)))

/-- Literal syntax naturality through fresh object binders and n-ary LFP tuple
binding. The native target formulas themselves commute, without a semantic
quotient or source syntax tags in the target. -/
theorem pattern_map (f : A ⟶ B) {r k} {P : Fin r → Nat} (p : Pattern A P k)
    {l} {Γ : Fin l → TargetSort} (σ : Fin k → TargetTerm A Γ .value)
    (h : TargetTerm A Γ .heap) :
    (pattern p σ h).map (signatureMap f) = pattern (p.map f)
      (fun i => (σ i).map (signatureMap f).toHom) (h.map (signatureMap f).toHom) := by
  induction p generalizing l with
  | base p => exact congrArg Silmaril.Logic.FirstOrderLFP.Formula.base (assertion_map f p σ h)
  | pred i args =>
      change Silmaril.Logic.FirstOrderLFP.Formula.pred i _ = Silmaril.Logic.FirstOrderLFP.Formula.pred i _
      exact congrArg (Silmaril.Logic.FirstOrderLFP.Formula.pred i) (compiledArgs_map f h σ args)
  | conj p q hp hq => exact congrArg₂ Silmaril.Logic.FirstOrderLFP.Formula.conj (hp σ h) (hq σ h)
  | disj p q hp hq => exact congrArg₂ Silmaril.Logic.FirstOrderLFP.Formula.disj (hp σ h) (hq σ h)
  | sep p q hp hq =>
      simp only [pattern,Pattern.map,Silmaril.Logic.FirstOrderLFP.Formula.map,
        joinFormula_map,hp,hq,map_liftHeap]
      rfl
  | wand p q hq =>
      simp only [pattern,Pattern.map,Silmaril.Logic.FirstOrderLFP.Formula.map,FOL.Formula.map,
        joinFormula_map,assertion_map,hq,map_liftHeap]
      rfl
  | ex p ih =>
      simp only [pattern,Pattern.map,Silmaril.Logic.FirstOrderLFP.Formula.map,
        ih,boundValues_map,map_liftTerm]
  | all p ih =>
      simp only [pattern,Pattern.map,Silmaril.Logic.FirstOrderLFP.Formula.map,
        ih,boundValues_map,map_liftTerm]
  | lfp body args ih =>
      simp only [pattern,Pattern.map,Silmaril.Logic.FirstOrderLFP.Formula.map,
        ih,bodyValues_map,tupleHeap_map]
      congr 1
      exact compiledArgs_map f h σ args

end Silmaril.Logic.Separation.Parameterized.FirstOrder
