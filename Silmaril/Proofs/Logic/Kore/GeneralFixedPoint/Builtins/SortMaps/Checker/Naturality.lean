module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Contexts.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.LiteralProfiles.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

private theorem admissible_recontext {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 s) :
    (Eq.mpr (congrArg₂ (fun sets objects : ContextData =>
      Matching.GeneralFixedPoint.Pattern scope.signature sets.2 objects.2 s) hP hΓ) p).admissible =
        p.admissible := by
  cases hP
  cases hΓ
  rfl

theorem reindexPattern_admissible {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (p : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) :
    (reindexPattern f p).admissible = p.admissible := by
  exact (admissible_recontext
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects) _).trans
    (Matching.SortMaps.Hom.admissible_generalPattern f.semantic.native p)

private theorem neg_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 s)
    (q : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 s) (hp : HEq p q) :
    HEq p.neg q.neg := by
  cases hP
  cases hΓ
  cases hp
  rfl

private theorem conj_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ)
    (p r : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 s)
    (q t : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 s)
    (hp : HEq p q) (hr : HEq r t) : HEq (p.conj r) (q.conj t) := by
  cases hP
  cases hΓ
  cases hp
  cases hr
  rfl

private theorem ex_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s bound : String} (hP : P = Q) (hΓ : Γ = Δ)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P.2 (Fin.cases bound Γ.2) s)
    (q : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 (Fin.cases bound Δ.2) s)
    (hp : HEq p q) : HEq (Matching.GeneralFixedPoint.Pattern.ex bound p) (Matching.GeneralFixedPoint.Pattern.ex bound q) := by
  cases hP
  cases hΓ
  cases hp
  rfl

private theorem objects_cast_heq {scope : Kore.Modules.Scope} {r k : Nat}
    {P : Fin r → String} {Γ Δ : Fin k → String} {s : String} (h : Γ = Δ)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P Γ s) :
    HEq p (h ▸ p : Matching.GeneralFixedPoint.Pattern scope.signature P Δ s) := by
  cases h
  rfl

theorem reindexPattern_neg {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (p : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) :
    reindexPattern f p.neg = (reindexPattern f p).neg := by
  apply eq_of_heq
  exact (reindexPattern_heq f p.neg).trans
    (neg_heq (namesData_mapNames f.semantic.native.sorts sets)
      (namesData_mapNames f.semantic.native.sorts objects)
      (reindexPattern f p) (Matching.SortMaps.Hom.generalPattern f.semantic.native p)
      (reindexPattern_heq f p)).symm

theorem reindexPattern_conj {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (p q : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) :
    reindexPattern f (p.conj q) = (reindexPattern f p).conj (reindexPattern f q) := by
  apply eq_of_heq
  exact (reindexPattern_heq f (p.conj q)).trans
    (conj_heq (namesData_mapNames f.semantic.native.sorts sets)
      (namesData_mapNames f.semantic.native.sorts objects)
      (reindexPattern f p) (reindexPattern f q)
      (Matching.SortMaps.Hom.generalPattern f.semantic.native p)
      (Matching.SortMaps.Hom.generalPattern f.semantic.native q)
      (reindexPattern_heq f p) (reindexPattern_heq f q)).symm

theorem reindexPattern_disj {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (p q : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) :
    reindexPattern f (p.disj q) = (reindexPattern f p).disj (reindexPattern f q) := by
  simp only [Matching.GeneralFixedPoint.Pattern.disj, reindexPattern_neg, reindexPattern_conj]

theorem reindexPattern_ex {A B : Package} (f : Step A B)
    {sets objects : Names} {s bound : String} (name : String)
    (p : @Kore.GeneralFixedPoint.Pattern A.base.scope sets ((name, bound) :: objects) s) :
    reindexPattern f (Matching.GeneralFixedPoint.Pattern.ex bound p) =
      Matching.GeneralFixedPoint.Pattern.ex (f.semantic.native.sorts bound) (reindexPattern f p) := by
  apply eq_of_heq
  exact (reindexPattern_heq f (Matching.GeneralFixedPoint.Pattern.ex bound p)).trans
    (ex_heq (namesData_mapNames f.semantic.native.sorts sets)
      (namesData_mapNames f.semantic.native.sorts objects)
      (reindexPattern f p)
      ((Matching.SortMaps.Hom.map_cons f.semantic.native bound (context objects)) ▸
        Matching.SortMaps.Hom.generalPattern f.semantic.native p)
      ((reindexPattern_heq f p).trans
        (objects_cast_heq (Matching.SortMaps.Hom.map_cons f.semantic.native bound (context objects)) _))).symm

theorem reindexPattern_all {A B : Package} (f : Step A B)
    {sets objects : Names} {s bound : String} (name : String)
    (p : @Kore.GeneralFixedPoint.Pattern A.base.scope sets ((name, bound) :: objects) s) :
    reindexPattern f p.all = (reindexPattern f p).all := by
  simp only [Matching.GeneralFixedPoint.Pattern.all, reindexPattern_neg, reindexPattern_ex f name]
  rfl

private theorem substitute_recontext {scope : Kore.Modules.Scope}
    {P P' Γ Γ' Q Q' Δ Δ' : ContextData} {s : String}
    (hP : P = P') (hΓ : Γ = Γ') (hQ : Q = Q') (hΔ : Δ = Δ')
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P'.2 Γ'.2 s)
    (σ : (i : Fin P'.1) → Matching.GeneralFixedPoint.Pattern scope.signature Q'.2 Δ'.2 (P'.2 i))
    (τ : (i : Fin Γ'.1) → Matching.GeneralFixedPoint.Pattern scope.signature Q'.2 Δ'.2 (Γ'.2 i)) :
    Eq.mpr (congrArg₂ (fun sets objects : ContextData =>
      Matching.GeneralFixedPoint.Pattern scope.signature sets.2 objects.2 s) hQ hΔ)
      (p.substitute σ τ) =
    (Eq.mpr (congrArg₂ (fun sets objects : ContextData =>
      Matching.GeneralFixedPoint.Pattern scope.signature sets.2 objects.2 s) hP hΓ) p).substitute
      (recontextFamily hP hQ hΔ σ) (recontextFamily hΓ hQ hΔ τ) := by
  cases hP
  cases hΓ
  cases hQ
  cases hΔ
  rfl

/-- Simultaneous alias substitutions commute in the actual named contexts.
The target family indices are the transported original finite coordinates. -/
theorem reindexPattern_substitute {A B : Package} (f : Step A B)
    {formalSets formalObjects sets objects : Names} {s : String}
    (p : @Kore.GeneralFixedPoint.Pattern A.base.scope formalSets formalObjects s)
    (σ : (i : Fin formalSets.length) → @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects
      (context formalSets i))
    (τ : (i : Fin formalObjects.length) → @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects
      (context formalObjects i)) :
    reindexPattern f (p.substitute σ τ) =
      (reindexPattern f p).substitute (reindexFamily f σ) (reindexFamily f τ) := by
  unfold reindexPattern
  rw [Matching.GeneralFixedPoint.SortNaturality.generalPattern_substitute]
  exact substitute_recontext
    (namesData_mapNames f.semantic.native.sorts formalSets)
    (namesData_mapNames f.semantic.native.sorts formalObjects)
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects) _ _ _

private theorem sets_cast_heq {scope : Kore.Modules.Scope} {r k : Nat}
    {P Q : Fin r → String} {Γ : Fin k → String} {s : String} (h : P = Q)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P Γ s) :
    HEq p (h ▸ p : Matching.GeneralFixedPoint.Pattern scope.signature Q Γ s) := by
  cases h
  rfl

private theorem full_mu_heq {scope : Kore.Modules.Scope} {r k : Nat}
    {P Q : Fin (r + 1) → String} {Γ : Fin k → String} (h : P = Q)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P Γ (P 0))
    (q : Matching.GeneralFixedPoint.Pattern scope.signature Q Γ (Q 0)) (hp : HEq p q) :
    HEq (Matching.GeneralFixedPoint.Pattern.mu p) (Matching.GeneralFixedPoint.Pattern.mu q) := by
  cases h
  cases hp
  rfl

private theorem full_nu_heq {scope : Kore.Modules.Scope} {r k : Nat}
    {P Q : Fin (r + 1) → String} {Γ : Fin k → String} (h : P = Q)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P Γ (P 0))
    (q : Matching.GeneralFixedPoint.Pattern scope.signature Q Γ (Q 0)) (hp : HEq p q) :
    HEq (Matching.GeneralFixedPoint.Pattern.nu p) (Matching.GeneralFixedPoint.Pattern.nu q) := by
  cases h
  cases hp
  rfl

private theorem context_mu_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature (Fin.cases s P.2) Γ.2 s)
    (q : Matching.GeneralFixedPoint.Pattern scope.signature (Fin.cases s Q.2) Δ.2 s)
    (hp : HEq p q) :
    HEq (Matching.GeneralFixedPoint.Pattern.mu p) (Matching.GeneralFixedPoint.Pattern.mu q) := by
  cases hP
  cases hΓ
  cases hp
  rfl

private theorem context_nu_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature (Fin.cases s P.2) Γ.2 s)
    (q : Matching.GeneralFixedPoint.Pattern scope.signature (Fin.cases s Q.2) Δ.2 s)
    (hp : HEq p q) :
    HEq (Matching.GeneralFixedPoint.Pattern.nu p) (Matching.GeneralFixedPoint.Pattern.nu q) := by
  cases hP
  cases hΓ
  cases hp
  rfl

/-- Reindexing retains the actual least fixed-point binder and its body. -/
theorem reindexPattern_mu {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (name : String)
    (p : @Kore.GeneralFixedPoint.Pattern A.base.scope ((name, s) :: sets) objects s) :
    reindexPattern f (Matching.GeneralFixedPoint.Pattern.mu p) =
      Matching.GeneralFixedPoint.Pattern.mu (reindexPattern f p) := by
  apply eq_of_heq
  refine (reindexPattern_heq f (Matching.GeneralFixedPoint.Pattern.mu p)).trans ?_
  have body := sets_cast_heq
    (Matching.SortMaps.Hom.map_cons f.semantic.native s (context sets))
    (Matching.SortMaps.Hom.generalPattern f.semantic.native p)
  exact (full_mu_heq (Matching.SortMaps.Hom.map_cons f.semantic.native s (context sets))
    _ _ body).trans
    (context_mu_heq (namesData_mapNames f.semantic.native.sorts sets)
      (namesData_mapNames f.semantic.native.sorts objects)
      (reindexPattern f p) _ ((reindexPattern_heq f p).trans body)).symm

/-- Reindexing retains the actual greatest fixed-point binder and its body. -/
theorem reindexPattern_nu {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (name : String)
    (p : @Kore.GeneralFixedPoint.Pattern A.base.scope ((name, s) :: sets) objects s) :
    reindexPattern f (Matching.GeneralFixedPoint.Pattern.nu p) =
      Matching.GeneralFixedPoint.Pattern.nu (reindexPattern f p) := by
  apply eq_of_heq
  refine (reindexPattern_heq f (Matching.GeneralFixedPoint.Pattern.nu p)).trans ?_
  have body := sets_cast_heq
    (Matching.SortMaps.Hom.map_cons f.semantic.native s (context sets))
    (Matching.SortMaps.Hom.generalPattern f.semantic.native p)
  exact (full_nu_heq (Matching.SortMaps.Hom.map_cons f.semantic.native s (context sets))
    _ _ body).trans
    (context_nu_heq (namesData_mapNames f.semantic.native.sorts sets)
      (namesData_mapNames f.semantic.native.sorts objects)
      (reindexPattern f p) _ ((reindexPattern_heq f p).trans body)).symm

private theorem basevar_context_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} (hP : P = Q) (hΓ : Γ = Δ) (i : Fin Δ.1) :
    HEq (.base (.var (Fin.cast (congrArg Sigma.fst hΓ).symm i)) :
        Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2
          (Γ.2 (Fin.cast (congrArg Sigma.fst hΓ).symm i)))
      (.base (.var i) : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 (Δ.2 i)) := by
  cases hP
  cases hΓ
  rfl

private theorem setvar_context_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} (hP : P = Q) (hΓ : Γ = Δ) (i : Fin Q.1) :
    HEq (.setvar (Fin.cast (congrArg Sigma.fst hP).symm i) :
        Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2
          (P.2 (Fin.cast (congrArg Sigma.fst hP).symm i)))
      (.setvar i : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 (Q.2 i)) := by
  cases hP
  cases hΓ
  rfl

private theorem sort_cast_heq {scope : Kore.Modules.Scope} {P Γ : ContextData}
    {s t : String} (h : s = t)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 s) :
    HEq p (h ▸ p : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 t) := by
  cases h
  rfl

private theorem reindexPattern_sort_cast_heq {A B : Package} (f : Step A B)
    {sets objects : Names} {s t : String} (h : s = t)
    (p : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) :
    HEq (reindexPattern f (h ▸ p)) (reindexPattern f p) := by
  cases h
  rfl

/-- An object-variable lookup keeps its finite coordinate and sort cast. -/
theorem reindexPattern_var {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (i : Fin objects.length)
    (same : context objects i = s) :
    reindexPattern f (same ▸ (.base (.var i) : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects (context objects i))) =
      ((context_mapNames f.semantic.native.sorts objects i).trans
          (congrArg f.semantic.native.sorts same)) ▸
        (.base (.var (mapIndex f.semantic.native.sorts objects i)) :
          @Kore.GeneralFixedPoint.Pattern B.base.scope (mapNames f.semantic.native.sorts sets)
            (mapNames f.semantic.native.sorts objects)
            (context (mapNames f.semantic.native.sorts objects) (mapIndex f.semantic.native.sorts objects i))) := by
  apply eq_of_heq
  exact (reindexPattern_sort_cast_heq f same _).trans
    ((reindexPattern_heq f (.base (.var i))).trans
      ((basevar_context_heq (namesData_mapNames f.semantic.native.sorts sets)
        (namesData_mapNames f.semantic.native.sorts objects) i).symm.trans
        (sort_cast_heq _ _)))

/-- A set-variable lookup keeps its namespace, coordinate and sort cast. -/
theorem reindexPattern_setvar {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (i : Fin sets.length)
    (same : context sets i = s) :
    reindexPattern f (same ▸ (.setvar i : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects (context sets i))) =
      ((context_mapNames f.semantic.native.sorts sets i).trans
          (congrArg f.semantic.native.sorts same)) ▸
        (.setvar (mapIndex f.semantic.native.sorts sets i) :
          @Kore.GeneralFixedPoint.Pattern B.base.scope (mapNames f.semantic.native.sorts sets)
            (mapNames f.semantic.native.sorts objects)
            (context (mapNames f.semantic.native.sorts sets) (mapIndex f.semantic.native.sorts sets i))) := by
  apply eq_of_heq
  exact (reindexPattern_sort_cast_heq f same _).trans
    ((reindexPattern_heq f (.setvar i)).trans
      ((setvar_context_heq (namesData_mapNames f.semantic.native.sorts sets)
        (namesData_mapNames f.semantic.native.sorts objects) i).symm.trans
        (sort_cast_heq _ _)))

private theorem firstOrder_cast_heq {scope : Kore.Modules.Scope} {k : Nat}
    {Γ Δ : Fin k → String} {s : String} (h : Γ = Δ)
    (p : Matching.FirstOrder.Pattern scope.signature Γ s) :
    HEq p (h ▸ p : Matching.FirstOrder.Pattern scope.signature Δ s) := by
  cases h
  rfl

private theorem firstOrder_var_heq {scope : Kore.Modules.Scope} {k : Nat}
    {Γ Δ : Fin k → String} (h : Γ = Δ) (i : Fin k) :
    HEq (.var i : Matching.FirstOrder.Pattern scope.signature Γ (Γ i))
      (.var i : Matching.FirstOrder.Pattern scope.signature Δ (Δ i)) := by
  cases h
  rfl

private theorem native_top {A B : Package} (f : Step A B) {k : Nat}
    {Γ : Fin k → String} {s : String} :
    Matching.SortMaps.Hom.pattern f.semantic.native
      (Matching.FirstOrder.Pattern.top : Matching.FirstOrder.Pattern A.base.scope.signature Γ s) =
      Matching.FirstOrder.Pattern.top := by
  simp only [Matching.FirstOrder.Pattern.top, Matching.SortMaps.Hom.pattern]
  apply congrArg (Matching.FirstOrder.Pattern.ex (f.semantic.native.sorts s))
  apply eq_of_heq
  exact (firstOrder_cast_heq (Matching.SortMaps.Hom.map_cons f.semantic.native s Γ) _).symm.trans
    (firstOrder_var_heq (Matching.SortMaps.Hom.map_cons f.semantic.native s Γ) 0)

private theorem native_bottom {A B : Package} (f : Step A B) {k : Nat}
    {Γ : Fin k → String} {s : String} :
    Matching.SortMaps.Hom.pattern f.semantic.native
      (Matching.FirstOrder.Pattern.bottom : Matching.FirstOrder.Pattern A.base.scope.signature Γ s) =
      Matching.FirstOrder.Pattern.bottom := by
  exact congrArg Matching.FirstOrder.Pattern.neg (native_top f)

private theorem top_context_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ) :
    HEq (.base Matching.FirstOrder.Pattern.top : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 s)
      (.base Matching.FirstOrder.Pattern.top : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 s) := by
  cases hP
  cases hΓ
  rfl

private theorem bottom_context_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ) :
    HEq (.base Matching.FirstOrder.Pattern.bottom : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 s)
      (.base Matching.FirstOrder.Pattern.bottom : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 s) := by
  cases hP
  cases hΓ
  rfl

theorem reindexPattern_top {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} :
    reindexPattern f (.base Matching.FirstOrder.Pattern.top : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) =
      .base Matching.FirstOrder.Pattern.top := by
  apply eq_of_heq
  refine (reindexPattern_heq f (.base Matching.FirstOrder.Pattern.top)).trans ?_
  have native : Matching.SortMaps.Hom.generalPattern f.semantic.native
      (.base Matching.FirstOrder.Pattern.top : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) =
      .base Matching.FirstOrder.Pattern.top := congrArg Matching.GeneralFixedPoint.Pattern.base (native_top f)
  exact (heq_of_eq native).trans
    (top_context_heq (namesData_mapNames f.semantic.native.sorts sets)
      (namesData_mapNames f.semantic.native.sorts objects)).symm

theorem reindexPattern_bottom {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} :
    reindexPattern f (.base Matching.FirstOrder.Pattern.bottom : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) =
      .base Matching.FirstOrder.Pattern.bottom := by
  apply eq_of_heq
  refine (reindexPattern_heq f (.base Matching.FirstOrder.Pattern.bottom)).trans ?_
  have native : Matching.SortMaps.Hom.generalPattern f.semantic.native
      (.base Matching.FirstOrder.Pattern.bottom : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects s) =
      .base Matching.FirstOrder.Pattern.bottom := congrArg Matching.GeneralFixedPoint.Pattern.base (native_bottom f)
  exact (heq_of_eq native).trans
    (bottom_context_heq (namesData_mapNames f.semantic.native.sorts sets)
      (namesData_mapNames f.semantic.native.sorts objects)).symm

private theorem operation_context_heq {scope : Kore.Modules.Scope}
    {R R' : ContextData} {s : String} (hR : R = R')
    (op : scope.signature.operations R.1 R.2 s)
    (op' : scope.signature.operations R'.1 R'.2 s) (value : op.val = op'.val) : HEq op op' := by
  cases hR
  exact heq_of_eq (Subtype.ext value)

private theorem app_context_heq {scope : Kore.Modules.Scope}
    {R R' P P' Γ Γ' : ContextData} {s : String}
    (hR : R = R') (hP : P = P') (hΓ : Γ = Γ')
    (op : scope.signature.operations R.1 R.2 s)
    (op' : scope.signature.operations R'.1 R'.2 s) (operations : HEq op op')
    (xs : (i : Fin R.1) → Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 (R.2 i))
    (xs' : (i : Fin R'.1) → Matching.GeneralFixedPoint.Pattern scope.signature P'.2 Γ'.2 (R'.2 i))
    (arguments : HEq xs xs') :
    HEq (Matching.GeneralFixedPoint.Pattern.app op xs) (Matching.GeneralFixedPoint.Pattern.app op' xs') := by
  cases hR
  cases hP
  cases hΓ
  cases operations
  cases arguments
  rfl

/-- An actual declared operation and its ordered arguments commute with the
sort action. Only its concrete declaration value identifies the target symbol. -/
theorem reindexPattern_app {A B : Package} (f : Step A B)
    {inputs : List String} {sets objects : Names} {s : String}
    (op : A.base.scope.signature.operations inputs.length inputs.get s)
    (op' : B.base.scope.signature.operations (inputs.map f.semantic.native.sorts).length
      (inputs.map f.semantic.native.sorts).get (f.semantic.native.sorts s))
    (value : op'.val = symbol f.semantic.native.sorts f.names op.val)
    (xs : (i : Fin inputs.length) → @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects (inputs.get i)) :
    reindexPattern f (.app op xs) = .app op' (reindexArguments f xs) := by
  apply eq_of_heq
  refine (reindexPattern_heq f (.app op xs)).trans ?_
  exact (app_context_heq (profileData_map f.semantic.native.sorts inputs)
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects)
    op' (f.semantic.native.operations op)
    (operation_context_heq (profileData_map f.semantic.native.sorts inputs) _ _
      (value.trans (f.operations op).symm))
    (reindexArguments f xs) (fun i => Matching.SortMaps.Hom.generalPattern f.semantic.native (xs i))
    (reindexArguments_heq f xs)).symm

private theorem nullary_app_heq {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s t : String} {inputs inputs' : Fin 0 → String}
    (hP : P = Q) (hΓ : Γ = Δ) (sort : s = t)
    (op : scope.signature.operations 0 inputs s)
    (op' : scope.signature.operations 0 inputs' t) (value : op.val = op'.val) :
    HEq (.app op (fun i => i.elim0) : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 s)
      (.app op' (fun i => i.elim0) : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 t) := by
  have profiles : inputs = inputs' := funext fun i => i.elim0
  cases profiles
  cases hP
  cases hΓ
  cases sort
  have operations : op = op' := Subtype.ext value
  cases operations
  rfl

/-- The literal constructor retains its declaration and its result-sort cast.
No default operation is supplied when a scope lacks the chosen declaration. -/
theorem reindexPattern_literal {A B : Package} (f : Step A B) {mi : Nat} {l : Literal}
    (op : @LiteralOperation A.base.bindings A.base.scope A.base.literals A.base.literalPrefix mi l)
    (op' : @LiteralOperation B.base.bindings B.base.scope B.base.literals B.base.literalPrefix mi l)
    (binding : (@LiteralOperation.binding B.base.bindings _ _ _ _ _ op') = (⟨symbol f.semantic.native.sorts f.names (@LiteralOperation.binding A.base.bindings _ _ _ _ _ op).symbol, (@LiteralOperation.binding A.base.bindings _ _ _ _ _ op).literal⟩ : LiteralBinding))
    {s : String} (same : @Literal.sort A.base.bindings l = s)
    (same' : @Literal.sort B.base.bindings l = f.semantic.native.sorts s)
    {sets objects : Names} :
    reindexPattern f (same ▸ (.app (@LiteralOperation.operation A.base.bindings _ _ _ _ _ op) (fun i => i.elim0) : @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects (@Literal.sort A.base.bindings l))) =
      same' ▸ (.app (@LiteralOperation.operation B.base.bindings _ _ _ _ _ op') (fun i => i.elim0) :
        @Kore.GeneralFixedPoint.Pattern B.base.scope (mapNames f.semantic.native.sorts sets)
          (mapNames f.semantic.native.sorts objects) (@Literal.sort B.base.bindings l)) := by
  apply eq_of_heq
  refine (reindexPattern_sort_cast_heq f same _).trans
    ((reindexPattern_heq f (.app (@LiteralOperation.operation A.base.bindings _ _ _ _ _ op) (fun i => i.elim0))).trans ?_)
  have empty : Matching.SortMaps.Hom.generalPattern f.semantic.native
      (.app (@LiteralOperation.operation A.base.bindings _ _ _ _ _ op) (fun i => i.elim0) :
        @Kore.GeneralFixedPoint.Pattern A.base.scope sets objects (@Literal.sort A.base.bindings l)) =
      .app (f.semantic.native.operations (@LiteralOperation.operation A.base.bindings _ _ _ _ _ op)) (fun i => i.elim0) := by
    apply congrArg (Matching.GeneralFixedPoint.Pattern.app _)
    funext i
    exact i.elim0
  refine (heq_of_eq empty).trans ?_
  have value : (f.semantic.native.operations (@LiteralOperation.operation A.base.bindings _ _ _ _ _ op)).val = (@LiteralOperation.operation B.base.bindings _ _ _ _ _ op').val := by
    rw [f.operations, (@LiteralOperation.declared A.base.bindings _ _ _ _ _ op), (@LiteralOperation.declared B.base.bindings _ _ _ _ _ op'), binding]
  exact (nullary_app_heq (namesData_mapNames f.semantic.native.sorts sets).symm
    (namesData_mapNames f.semantic.native.sorts objects).symm
    (literal_sort_map f.semantic l).symm _ _ value).trans (sort_cast_heq same' _)

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
