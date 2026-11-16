module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Coherence

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {A B : SortMaps.Signature}

theorem fixedPattern_context_cast (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ Δ : Fin k → A.sorts} {s : A.sorts} (h : Γ = Δ)
    (p : FixedPoint.Pattern A.symbols P Γ s) :
    f.fixedPattern (h ▸ p) = congrArg (f.sorts ∘ ·) h ▸ f.fixedPattern p := by cases h; rfl

theorem cast_conj {S : Type} {A : Algebraic.ManySorted.Signature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p q : FixedPoint.Pattern A P Γ s) :
    (h ▸ p.conj q) = (h ▸ p).conj (h ▸ q) := by cases h; rfl

theorem cast_ex {S : Type} {A : Algebraic.ManySorted.Signature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s bound : S} (h : Γ = Δ)
    (p : FixedPoint.Pattern A P (Fin.cases bound Γ) s) :
    (h ▸ FixedPoint.Pattern.ex bound p) = FixedPoint.Pattern.ex bound (congrArg (fun Γ : Fin k → S => (Fin.cases bound Γ : Fin (k+1) → S)) h ▸ p) := by cases h; rfl

theorem cast_app {S : Type} {A : Algebraic.ManySorted.Signature S} {r k n : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {inputs : Fin n → S} {s : S} (h : Γ = Δ)
    (op : A.operations n inputs s) (args : ∀ i, FixedPoint.Pattern A P Γ (inputs i)) :
    (h ▸ FixedPoint.Pattern.app op args) = .app op (fun i => h ▸ args i) := by cases h; rfl

theorem cast_twice {S : Type} {A : Algebraic.ManySorted.Signature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ Θ : Fin k → S} {s : S} (h : Γ = Δ) (g : Δ = Θ)
    (p : FixedPoint.Pattern A P Γ s) :
    (g ▸ (h ▸ p)) = (h.trans g) ▸ p := by cases h; cases g; rfl

theorem blockContext_map (f : A ⟶ B) {k n : Nat} (Γ : Fin k → A.sorts) (w : Fin n → A.sorts) :
    f.sorts ∘ blockContext Γ w = blockContext (f.sorts ∘ Γ) (f.sorts ∘ w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      exact Fin.cases rfl (fun j => congrFun (ih (w ∘ Fin.succ)) j) i

theorem bindPrefix_map (f : A ⟶ B) {r k n : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {w : Fin n → A.sorts} {s : A.sorts}
    (body : FixedPoint.Pattern A.symbols P (blockContext Γ w) s) :
    f.fixedPattern (bindPrefix body) = bindPrefix ((blockContext_map f Γ w) ▸ f.fixedPattern body) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change f.fixedPattern (bindPrefix (.ex (w 0) body)) = _
      rw [ih]
      simp only [SortMaps.Hom.fixedPattern, cast_ex, cast_twice]
      rfl

theorem cast_sortedVar {S : Type} {A : Algebraic.ManySorted.Signature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (hΓ : Γ = Δ) (i : Fin k)
    (h : Γ i = s) (g : Δ i = s) :
    (hΓ ▸ Eq.mp (congrArg (fun t => FixedPoint.Pattern A P Γ t) h) (.base (.var i))) =
      Eq.mp (congrArg (fun t => FixedPoint.Pattern A P Δ t) g) (.base (.var i)) := by
  cases hΓ
  rfl

theorem fixedPattern_sortedVar (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {s : A.sorts} (i : Fin k) (h : Γ i = s) :
    f.fixedPattern (Eq.mp (congrArg (fun t => FixedPoint.Pattern A.symbols P Γ t) h) (.base (.var i))) =
      Eq.mp (congrArg (fun t => FixedPoint.Pattern B.symbols (f.sorts ∘ P) (f.sorts ∘ Γ) t)
        (congrArg f.sorts h)) (.base (.var i)) := by cases h; rfl

theorem prefixPack_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : Profile S) :
    (blockContext_map (signatureMap f) (objContext Γ) (objContext p.sorts)) ▸
      (signatureMap f).fixedPattern (prefixPack (P := P) (Γ := Γ) p) =
      prefixPack (P := fun i => (P i).map f) (Γ := f.sorts ∘ Γ) (p.map f) := by
  change ((blockContext_map (signatureMap f) (objContext Γ) (objContext p.sorts)) ▸ FixedPoint.Pattern.app (Operation.pack (p.map f))
    (fun i => (signatureMap f).fixedPattern (prefixVar p i))) = _
  erw [cast_app]
  congr 1
  funext i
  unfold prefixVar
  rw [fixedPattern_sortedVar (signatureMap f) (prefixIndex i)
    (blockContext_prefix (objContext Γ) (objContext p.sorts) i)]
  exact cast_sortedVar (blockContext_map (signatureMap f) (objContext Γ) (objContext p.sorts))
    (prefixIndex i) (congrArg (signatureMap f).sorts
      (blockContext_prefix (objContext Γ) (objContext p.sorts) i))
    (blockContext_prefix (objContext (f.sorts ∘ Γ)) (objContext (p.map f).sorts) i)
theorem blockRen_map {S T : FOL.Signature} (f : S ⟶ T) {n k : Nat}
    {Γ : Fin k → S.S} {w : Fin n → S.S} {Δ : Fin (n+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = w) (hp : Δ ∘ Fin.natAdd n = Γ) :
    transportRen rfl (blockContext_map (signatureMap f) (objContext Γ) (objContext w))
      (mapRen (signatureMap f) (blockRen (Δ := objContext Δ) (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp))) =
      blockRen (Γ := objContext (f.sorts ∘ Γ)) (w := objContext (f.sorts ∘ w))
        (Δ := objContext (f.sorts ∘ Δ))
        (congrArg (objSort ∘ ·) (congrArg (f.sorts ∘ ·) ht))
        (congrArg (objSort ∘ ·) (congrArg (f.sorts ∘ ·) hp)) := by
  funext i
  apply Subtype.ext
  rw [transportRen_val]
  rfl

theorem tupleBody_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P' : Fin (r+1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FixedPoint.Pattern (signature S).symbols (setContext P') (objContext Δ) (.base .truth)) :
    (signatureMap f).fixedPattern (tupleBody ht hp body) =
      tupleBody (congrArg (f.sorts ∘ ·) ht) (congrArg (f.sorts ∘ ·) hp)
        ((signatureMap f).fixedPattern body) := by
  unfold tupleBody
  rw [bindPrefix_map]
  change bindPrefix ((blockContext_map (signatureMap f) (objContext Γ) (objContext (P' 0).sorts)) ▸
    (((signatureMap f).fixedPattern (prefixPack (P' 0))).conj
      ((signatureMap f).fixedPattern (.app (Operation.liftTruth (P' 0)) (fun _ => body.renameObjects
        (blockRen (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp))))))) = _
  rw [cast_conj]
  erw [prefixPack_map]
  congr 2
  erw [cast_app]
  congr 1
  funext i
  have hm := fixedPattern_rename (signatureMap f) body
    (blockRen (Δ := objContext Δ) (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp))
  have hc := congrArg (fun p => (blockContext_map (signatureMap f) (objContext Γ) (objContext (P' 0).sorts)) ▸ p) hm
  refine hc.trans ?_
  rw [← rename_context rfl (blockContext_map (signatureMap f) (objContext Γ) (objContext (P' 0).sorts))]
  rw [blockRen_map f ht hp]

theorem basePattern_map {S T : FOL.Signature} (f : S ⟶ T) {k : Nat}
    {Γ : Fin k → GuardedFOL.MatchingSort S} {s : GuardedFOL.MatchingSort S}
    (p : FirstOrder.Pattern (GuardedFOL.signature S).symbols Γ s) :
    (signatureMap f).pattern ((baseSignature S).pattern p) =
      (baseSignature T).pattern ((GuardedFOL.signatureMap f).pattern p) := by
  rw [← SortMaps.Hom.pattern_comp, ← SortMaps.Hom.pattern_comp]
  rfl

theorem term_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} {s : S.S} (t : EQ.Term S.toSignature Γ s) :
    (signatureMap f).fixedPattern (term (P := P) t) = term (P := fun i => (P i).map f) (t.map f.toHom) := by
  change FixedPoint.Pattern.base ((signatureMap f).pattern ((baseSignature S).pattern (GuardedFOL.term t))) = _
  rw [basePattern_map, GuardedFOL.term_map]

theorem packTerms_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} {p : Profile S}
    (args : ∀ j, EQ.Term S.toSignature Γ (p.sorts j)) :
    (signatureMap f).fixedPattern (packTerms (P := P) args) =
      packTerms (P := fun i => (P i).map f) (fun j => (args j).map f.toHom) := by
  change FixedPoint.Pattern.app (Operation.pack (p.map f))
    (fun i => (signatureMap f).fixedPattern (term (P := P) (args i))) = _
  congr 1
  funext i
  exact term_map f (P := P) (args i)

theorem all_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P : Fin r → Profile S} (Δ : Fin (k+1) → S.S)
    (p : FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Δ) (.base .truth)) :
    (signatureMap f).fixedPattern (.all (objSort (Δ 0)) ((context_extend Δ) ▸ p)) =
      .all (objSort (f.sorts (Δ 0))) ((context_extend (f.sorts ∘ Δ)) ▸ (signatureMap f).fixedPattern p) := by
  change FixedPoint.Pattern.all (objSort (f.sorts (Δ 0)))
    ((SortMaps.Hom.map_cons (signatureMap f) (objSort (Δ 0)) (objContext (Δ ∘ Fin.succ))) ▸
      (signatureMap f).fixedPattern ((context_extend Δ) ▸ p)) = _
  rw [fixedPattern_context_cast, cast_twice]

theorem ex_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P : Fin r → Profile S} (Δ : Fin (k+1) → S.S)
    (p : FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Δ) (.base .truth)) :
    (signatureMap f).fixedPattern (.ex (objSort (Δ 0)) ((context_extend Δ) ▸ p)) =
      .ex (objSort (f.sorts (Δ 0))) ((context_extend (f.sorts ∘ Δ)) ▸ (signatureMap f).fixedPattern p) := by
  change FixedPoint.Pattern.ex (objSort (f.sorts (Δ 0)))
    ((SortMaps.Hom.map_cons (signatureMap f) (objSort (Δ 0)) (objContext (Δ ∘ Fin.succ))) ▸
      (signatureMap f).fixedPattern ((context_extend Δ) ▸ p)) = _
  rw [fixedPattern_context_cast, cast_twice]

theorem activePattern_map {S T : FOL.Signature} (f : S ⟶ T) {k : Nat}
    (Δ : Fin (k+1) → S.S) :
    (signatureMap f).pattern ((baseSignature S).pattern (GuardedFOL.activeGuard Δ)) =
      (baseSignature T).pattern (GuardedFOL.activeGuard (f.sorts ∘ Δ)) := by
  rw [basePattern_map, GuardedFOL.activeGuard_map]

theorem inactivePattern_map {S T : FOL.Signature} (f : S ⟶ T) {k : Nat}
    (Δ : Fin (k+1) → S.S) :
    (signatureMap f).pattern ((baseSignature S).pattern (.neg (GuardedFOL.activeGuard Δ))) =
      (baseSignature T).pattern (.neg (GuardedFOL.activeGuard (f.sorts ∘ Δ))) := by
  change FirstOrder.Pattern.neg ((signatureMap f).pattern ((baseSignature S).pattern (GuardedFOL.activeGuard Δ))) = _
  rw [activePattern_map]
  rfl

theorem formula_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : FirstOrderLFP.Formula S P Γ) :
    (signatureMap f).fixedPattern (formula p) = formula (p.map f) := by
  induction p with
  | base p =>
      change FixedPoint.Pattern.base ((signatureMap f).pattern ((baseSignature S).pattern (GuardedFOL.formula p))) = _
      rw [basePattern_map, GuardedFOL.formula_map]
      rfl
  | pred i args =>
      change tupleDefined (.conj ((signatureMap f).fixedPattern (packTerms args)) (.setvar i)) = _
      rw [packTerms_map]
      rfl
  | conj p q hp hq => exact congrArg₂ FixedPoint.Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ FixedPoint.Pattern.disj hp hq
  | @all r k P Δ p ih =>
      show (signatureMap f).fixedPattern (formula (FirstOrderLFP.Formula.all p)) =
        formula ((FirstOrderLFP.Formula.all p).map f)
      rw [formula, all_map]
      change FixedPoint.Pattern.all (objSort (f.sorts (Δ 0))) ((context_extend (f.sorts ∘ Δ)) ▸
        (show FixedPoint.Pattern (signature T).symbols (setContext (fun i => (P i).map f))
          (objContext (f.sorts ∘ Δ)) (.base .truth) from .disj
          (.base ((signatureMap f).pattern ((baseSignature S).pattern (.neg (GuardedFOL.activeGuard Δ)))))
          ((signatureMap f).fixedPattern (formula p)))) = _
      rw [inactivePattern_map, ih]
      rfl
  | @ex r k P Δ p ih =>
      show (signatureMap f).fixedPattern (formula (FirstOrderLFP.Formula.ex p)) =
        formula ((FirstOrderLFP.Formula.ex p).map f)
      rw [formula, ex_map]
      change FixedPoint.Pattern.ex (objSort (f.sorts (Δ 0))) ((context_extend (f.sorts ∘ Δ)) ▸
        (show FixedPoint.Pattern (signature T).symbols (setContext (fun i => (P i).map f))
          (objContext (f.sorts ∘ Δ)) (.base .truth) from .conj
          (.base ((signatureMap f).pattern ((baseSignature S).pattern (GuardedFOL.activeGuard Δ))))
          ((signatureMap f).fixedPattern (formula p)))) = _
      rw [activePattern_map, ih]
      rfl
  | lfp ht hp body args ih =>
      change tupleDefined (.conj ((signatureMap f).fixedPattern (packTerms args))
        (.mu ((signatureMap f).fixedPattern (tupleBody ht hp (formula body))))) = _
      rw [packTerms_map, tupleBody_map, ih]
      rfl

end Silmaril.Logic.Matching.GuardedLFP
