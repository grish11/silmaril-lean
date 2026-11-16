module

public import Silmaril.Logic.Matching.GuardedLFP.Translation
public import Silmaril.Logic.Matching.GuardedLFP.Retraction
public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Tuples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

abbrev tupleEncode (M : Model S) (p : Profile S) :
    FirstOrderLFP.Tuple (decode M) p → M.base.carrier (.tuple p) := fun x => (pack M p x).val

theorem tupleEncode_injective (M : Model S) (p : Profile S) :
    Function.Injective (tupleEncode M p) := by
  intro x y h
  have same : pack M p x = pack M p y := Subtype.ext h
  exact (project_pack M p x).symm.trans ((congrArg (project M p) same).trans (project_pack M p y))

/-- Free native set variables may contain arbitrary inactive padding. -/
def restrictEnv (M : Model S) {r : Nat} {P : Fin r → Profile S}
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) : FirstOrderLFP.RelEnv (decode M) P :=
  fun i => restrict (tupleEncode M (P i)) (η i)

theorem term_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} {s : S.S} (t : EQ.Term S.toSignature Γ s)
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) :
    (term (P := P) t).denote M.base (fun i => (v i).val) η =
      {(t.eval (decode M).toStructure.toAlgebra v).val} := by
  change M.base.denote _ ((baseSignature S).pattern (GuardedFOL.term t)) = _
  exact (SortMaps.Hom.denote_pattern (baseSignature S) M.base (GuardedFOL.term t) _).trans
    (GuardedFOL.term_denote (guardedModel M) t v)

theorem tupleDefined_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → MatchingSort S} {p : Profile S}
    (t : FixedPoint.Pattern (signature S).symbols (setContext P) Γ (.tuple p))
    (v : FixedPoint.ObjEnv (signature S).symbols M.base Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (tupleDefined t).denote M.base v η ↔ ∃ x, x ∈ t.denote M.base v η := by
  constructor
  · rintro ⟨values, hv, _⟩
    exact ⟨values 0, hv 0⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun _ => x, fun _ => hx, ?_⟩
    rw [M.tupleDefined]
    trivial

theorem packTerms_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} {p : Profile S} (args : ∀ j, EQ.Term S.toSignature Γ (p.sorts j))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) :
    (packTerms args).denote M.base (fun i => (v i).val) η =
      {tupleEncode M p (fun j => (args j).eval (decode M).toStructure.toAlgebra v)} := by
  change FixedPoint.application M.base (.pack p) _ = _
  apply Set.ext
  intro y
  constructor
  · rintro ⟨values, hv, hy⟩
    have same : values = fun j => ((args j).eval (decode M).toStructure.toAlgebra v).val :=
      funext fun j => by
        have hj := hv j
        change values j ∈ (term (args j)).denote M.base (fun i => (v i).val) η at hj
        rw [term_denote] at hj
        exact hj
    subst values
    exact pack_graph M p _ ▸ hy
  · intro hy
    refine ⟨_, (fun j => (term_denote M (args j) v η).symm ▸ Set.mem_singleton _), ?_⟩
    exact (pack_graph M p _).symm ▸ hy

theorem variable_cast_denote {T : Type} {A : Algebraic.ManySorted.Signature T}
    (M : FixedPoint.Model A) {r k : Nat} {P : Fin r → T} {Γ : Fin k → T}
    (j : Fin k) {t : T} (h : Γ j = t) (v : FixedPoint.ObjEnv A M Γ)
    (η : FixedPoint.SetEnv A M P) :
    (Eq.mp (congrArg (fun s => FixedPoint.Pattern A P Γ s) h) (.base (.var j))).denote M v η =
      {h ▸ v j} := by
  cases h
  rfl

theorem prefixPack_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} (p : Profile S)
    (v : FixedPoint.ObjEnv (signature S).symbols M.base (objContext Γ))
    (x : ∀ i, M.base.carrier (objSort (p.sorts i)))
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) :
    (prefixPack (P := P) (Γ := Γ) p).denote M.base (blockEnv M.base.carrier v x) η =
      M.base.operation (.pack p) x := by
  have component (i : Fin p.arity) :
      (prefixVar (P := P) (Γ := Γ) p i).denote M.base (blockEnv M.base.carrier v x) η = {x i} := by
    unfold prefixVar
    rw [variable_cast_denote M.base (prefixIndex i)
      (blockContext_prefix (objContext Γ) (objContext p.sorts) i)
      (blockEnv M.base.carrier v x) η]
    apply congrArg Set.singleton
    exact eq_of_heq ((value_cast_heq M.base.carrier
      (blockContext_prefix (objContext Γ) (objContext p.sorts) i) _).trans
        (blockEnv_prefix M.base.carrier v x i))
  change FixedPoint.application M.base (.pack p) _ = _
  apply Set.ext
  intro y
  constructor
  · rintro ⟨values, hv, hy⟩
    have same : values = x := funext fun i => by
      have hi := hv i
      change values i ∈ (prefixVar (P := P) (Γ := Γ) p i).denote M.base (blockEnv M.base.carrier v x) η at hi
      rw [component] at hi
      exact hi
    subst values
    exact hy
  · intro hy
    refine ⟨x, ?_, hy⟩
    intro i
    change x i ∈ (prefixVar (P := P) (Γ := Γ) p i).denote M.base (blockEnv M.base.carrier v x) η
    rw [component]
    exact Set.mem_singleton _

theorem active_value_heq (M : Model S) {a b : S.S} (hs : a = b)
    (x : (decode M).toStructure.carrier a) (y : (decode M).toStructure.carrier b)
    (h : HEq x y) : HEq x.val y.val := by
  cases hs
  exact heq_of_eq (congrArg Subtype.val (eq_of_heq h))

theorem blockPull_eq (M : Model S) {n k : Nat} {w : Fin n → S.S} {Γ : Fin k → S.S}
    {Δ : Fin (n+k) → S.S} (ht : Δ ∘ Fin.castAdd k = w)
    (hp : Δ ∘ Fin.natAdd n = Γ) (x : FirstOrderLFP.ObjEnv (decode M) w)
    (v : FirstOrderLFP.ObjEnv (decode M) Γ) (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
    (hθ : FirstOrderLFP.Extends θ x v) :
    FixedPoint.Ren.pull M.base.carrier
      (blockEnv M.base.carrier (fun i => (v i).val) (fun i => (x i).val))
      (blockRen (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp)) =
        (fun i => (θ i).val) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact eq_of_heq ((blockPull_prefix M.base.carrier
      (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp) _ _ j).trans
        (active_value_heq M (congrFun ht j) _ _ (hθ.1 j)).symm)
  · exact eq_of_heq ((blockPull_ambient M.base.carrier
      (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp) _ _ j).trans
        (active_value_heq M (congrFun hp j) _ _ (hθ.2 j)).symm)

theorem pred_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} (i : Fin r) (args : ∀ j, EQ.Term S.toSignature Γ ((P i).sorts j))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula (.pred i args)).denote M.base (fun j => (v j).val) η ↔
      v ∈ (FirstOrderLFP.Formula.pred i args).denote (decode M) (restrictEnv M η) := by
  rw [formula, tupleDefined_denote]
  change (∃ x, x ∈ (packTerms args).denote M.base _ η ∩ η i) ↔ _
  rw [packTerms_denote]
  constructor
  · rintro ⟨x, hx, hi⟩
    change x = _ at hx
    subst x
    exact hi
  · intro h
    exact ⟨_, rfl, h⟩
end Silmaril.Logic.Matching.GuardedLFP
