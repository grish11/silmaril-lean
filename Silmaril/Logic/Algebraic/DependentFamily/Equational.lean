module

public import Silmaril.Logic.Algebraic.DependentFamily.Defs
public import Silmaril.Logic.Algebraic.ManySorted.Defs
public import Silmaril.Logic.Institution.Morphism

@[expose] public section
namespace Silmaril.Logic.Algebraic.DependentFamily.Equational
open CategoryTheory

variable {S : Type}
abbrev arity (_ : S) : Nat := 0
abbrev sort (s : S) : SortExpr S arity 0 := ⟨s, id⟩

def signature (A : Silmaril.Logic.Algebraic.ManySorted.Signature S) : Signature S arity where
  operations _ n inputs output := A.operations n (fun i => (inputs i).symbol) output.symbol

def signatures : Silmaril.Logic.Algebraic.ManySorted.Signature S ⥤ Signature S arity where
  obj := signature
  map f := ⟨fun op => f.operations op⟩
  map_id _ := Signature.Hom.ext _ _ _ _ (fun _ _ _ _ _ => rfl)
  map_comp _ _ := Signature.Hom.ext _ _ _ _ (fun _ _ _ _ _ => rfl)

variable {A : Silmaril.Logic.Algebraic.ManySorted.Signature S}

def term {n : Nat} {Γ : Fin n → S} {s : S} :
    Silmaril.Logic.Algebraic.ManySorted.Term A Γ s → Term (signature A) (fun i => sort (Γ i) : Fin n → SortExpr S arity 0) (sort s)
  | .var i => .var i
  | .app op args => Term.app (A := signature A) (Γ := fun i => sort (Γ i))
      (inputs := fun _ => sort _) (output := sort _) op (fun i : Fin 0 => i)
      (fun i => term (args i))

/-- Ordinary algebras give dependent-family models with a singleton base. -/
def model (M : Silmaril.Logic.Algebraic.ManySorted.Model A) : Model (signature A) where
  Base := PUnit
  carrier s _ := M.carrier s
  operation op _ args := M.operation op args

theorem eval_term (M : Silmaril.Logic.Algebraic.ManySorted.Model A)
    {n : Nat} {Γ : Fin n → S} {s : S}
    (v : (i : Fin n) → M.carrier (Γ i)) (t : Silmaril.Logic.Algebraic.ManySorted.Term A Γ s) :
    (model M).eval (fun i => Fin.elim0 i) v (term t) = M.eval v t := by
  induction t with
  | var => rfl
  | app op args ih =>
      simp only [term, Model.eval, model, Silmaril.Logic.Algebraic.ManySorted.Model.eval]
      congr
      funext i
      exact ih i

def equation (e : Silmaril.Logic.Algebraic.ManySorted.Equation A) : Equation (signature A) :=
  ⟨0, e.variableCount, fun i => sort (e.context i), sort e.sort, term e.lhs, term e.rhs⟩

theorem satisfaction (M : Silmaril.Logic.Algebraic.ManySorted.Model A)
    (e : Silmaril.Logic.Algebraic.ManySorted.Equation A) :
    Equation.Satisfies (model M) (equation e) ↔
      Silmaril.Logic.Algebraic.ManySorted.Equation.Satisfies M e := by
  constructor
  · intro h v
    exact (eval_term M v e.lhs).symm.trans ((h Fin.elim0 v).trans (eval_term M v e.rhs))
  · intro h b v
    have hb : b = Fin.elim0 := funext fun i => Fin.elim0 i
    cases hb
    exact (eval_term M v e.lhs).trans ((h v).trans (eval_term M v e.rhs).symm)

/-- No ordinary algebraic model is lost by the zero-arity embedding. -/
theorem models_preserved (M : Silmaril.Logic.Algebraic.ManySorted.Model A)
    (axioms : Set (Silmaril.Logic.Algebraic.ManySorted.Equation A))
    (h : ∀ e ∈ axioms, Silmaril.Logic.Algebraic.ManySorted.Equation.Satisfies M e) :
    ∀ e ∈ axioms, Equation.Satisfies (model M) (equation e) :=
  fun e he => (satisfaction M e).2 (h e he)

/-- In the zero-arity fragment all sort indices can be erased. -/
def eraseTerm {k n} {Γ : Fin n → SortExpr S arity k} {s} :
    Term (signature A) Γ s →
      Silmaril.Logic.Algebraic.ManySorted.Term A (fun i => (Γ i).symbol) s.symbol
  | .var i => .var i
  | .app op _ args => .app op (fun i => eraseTerm (args i))

def eraseEquation (e : Equation (signature A)) : Silmaril.Logic.Algebraic.ManySorted.Equation A :=
  ⟨e.variableCount, fun i => (e.context i).symbol, e.sort.symbol,
    eraseTerm e.lhs, eraseTerm e.rhs⟩

theorem erase_term {n} {Γ : Fin n → S} {s}
    (t : Silmaril.Logic.Algebraic.ManySorted.Term A Γ s) : eraseTerm (term t) = t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Silmaril.Logic.Algebraic.ManySorted.Term.app op) (funext ih)

theorem erase_equation (e : Silmaril.Logic.Algebraic.ManySorted.Equation A) :
    eraseEquation (equation e) = e := by
  cases e
  simp only [equation, eraseEquation, erase_term]

/-- The sentence inclusion has an actual left inverse. -/
theorem equation_injective : Function.Injective (equation (A := A)) := by
  intro e f h
  exact (erase_equation e).symm.trans ((congrArg eraseEquation h).trans (erase_equation f))

theorem eval_erase (M : Silmaril.Logic.Algebraic.ManySorted.Model A)
    {k n} {Γ : Fin n → SortExpr S arity k} {s}
    (b : Fin k → PUnit) (v : (i : Fin n) → M.carrier (Γ i).symbol)
    (t : Term (signature A) Γ s) :
    (model M).eval b v t = M.eval v (eraseTerm t) := by
  induction t with
  | var => rfl
  | app op ρ args ih =>
      exact congrArg (M.operation op) (funext ih)

theorem erase_satisfaction (M : Silmaril.Logic.Algebraic.ManySorted.Model A)
    (e : Equation (signature A)) :
    Silmaril.Logic.Algebraic.ManySorted.Equation.Satisfies M (eraseEquation e) ↔
      Equation.Satisfies (model M) e := by
  constructor
  · intro h b v
    exact (eval_erase M b v e.lhs).trans ((h v).trans (eval_erase M b v e.rhs).symm)
  · intro h v
    exact (eval_erase M (fun _ => PUnit.unit) v e.lhs).symm.trans
      ((h (fun _ => PUnit.unit) v).trans (eval_erase M (fun _ => PUnit.unit) v e.rhs))

def modelFunctor : Silmaril.Logic.Algebraic.ManySorted.Model A ⥤ Model (signature A) where
  obj := model
  map {M N} h := (⟨id, fun s _ x => h.map s x,
    fun op _ args => h.operation op args⟩ : Model.Hom (model M) (model N))
  map_id _ := Model.Hom.ext _ _ rfl HEq.rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl HEq.rfl

theorem eraseTerm_map {B : Silmaril.Logic.Algebraic.ManySorted.Signature S} (f : A ⟶ B)
    {k n} {Γ : Fin n → SortExpr S arity k} {s} (t : Term (signature A) Γ s) :
    eraseTerm (Term.map (signatures.map f) t) =
      Silmaril.Logic.Algebraic.ManySorted.Term.map f (eraseTerm t) := by
  induction t with
  | var => rfl
  | app op ρ args ih =>
      exact congrArg (Silmaril.Logic.Algebraic.ManySorted.Term.app (f.operations op)) (funext ih)

theorem eraseEquation_map {B : Silmaril.Logic.Algebraic.ManySorted.Signature S} (f : A ⟶ B)
    (e : Equation (signature A)) :
    eraseEquation (Equation.map (signatures.map f) e) =
      Silmaril.Logic.Algebraic.ManySorted.Equation.map f (eraseEquation e) := by
  cases e with
  | mk k n Γ s l r =>
      exact congrArg₂
        (fun l r => (⟨n, fun i => (Γ i).symbol, s.symbol, l, r⟩ :
          Silmaril.Logic.Algebraic.ManySorted.Equation B))
        (eraseTerm_map (A := A) f l) (eraseTerm_map (A := A) f r)

/-- A genuine institution morphism: erase indices on sentences and interpret
ordinary models over the singleton base. The forward sentence inclusion above
is an injective section of this erasure. -/
def morphism (S : Type) : Silmaril.Logic.Institution.Inst.Hom
    ⟨Silmaril.Logic.Algebraic.ManySorted.Signature S, Silmaril.Logic.Algebraic.ManySorted.institution S⟩
    ⟨Signature S arity, institution S arity⟩ where
  Φ := signatures
  η := {
    app := fun _ => ⟨eraseEquation, modelFunctor, erase_satisfaction⟩
    naturality := by
      intro A B f
      apply Silmaril.Logic.Institution.Room.hom_ext
      · funext e
        exact eraseEquation_map f e
      · apply Functor.hext (fun _ => rfl)
        intro M N h
        exact HEq.rfl }

end Silmaril.Logic.Algebraic.DependentFamily.Equational
