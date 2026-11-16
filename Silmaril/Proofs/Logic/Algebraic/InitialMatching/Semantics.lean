module

public import Silmaril.Logic.Algebraic.Initial.Matching.Models
public import Silmaril.Logic.Algebraic.Initial.Matching.Algebra

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching
open CategoryTheory

/-- The native existential variable pattern denotes the whole carrier. -/
theorem top_denote {A : Signature} (M : Model A) {r k : Nat}
    (v : Fin k → M.native.carrier ()) (η : Fin r → Set (M.native.carrier ())) :
    (top : Pat A r k).denote M.native v η = Set.univ := by
  ext x
  change (∃ value, x = value) ↔ True
  simp

theorem bottom_denote {A : Signature} (M : Model A) {r k : Nat}
    (v : Fin k → M.native.carrier ()) (η : Fin r → Set (M.native.carrier ())) :
    (bottom : Pat A r k).denote M.native v η = ∅ := by
  ext x
  change ((∃ value, x = value) ∧ ¬ ∃ value, x = value) ↔ False
  simp

theorem disjunction_mem {A : Signature} (M : Model A) {r k : Nat}
    (ps : List (Pat A r k)) (v : Fin k → M.native.carrier ())
    (η : Fin r → Set (M.native.carrier ())) (x : M.native.carrier ()) :
    x ∈ (disjunction ps).denote M.native v η ↔ ∃ p ∈ ps, x ∈ p.denote M.native v η := by
  induction ps with
  | nil => simp [disjunction, bottom_denote]
  | cons p ps ih =>
    change (x ∈ p.denote M.native v η ∨ x ∈ (disjunction ps).denote M.native v η) ↔ _
    simp [ih]

theorem conjunction_mem {A : Signature} (M : Model A) {r k : Nat}
    (ps : List (Pat A r k)) (v : Fin k → M.native.carrier ())
    (η : Fin r → Set (M.native.carrier ())) (x : M.native.carrier ()) :
    x ∈ (conjunction ps).denote M.native v η ↔ ∀ p ∈ ps, x ∈ p.denote M.native v η := by
  induction ps with
  | nil => simp [conjunction, top_denote]
  | cons p ps ih =>
    change (x ∈ p.denote M.native v η ∧ x ∈ (conjunction ps).denote M.native v η) ↔ _
    simp [ih]

/-- Universal ceil turns overlap of singleton patterns into equality. -/
theorem equal_mem {A : Signature} (M : Model A) {k : Nat}
    (v : Fin k → M.native.carrier ()) (a b : Raw A k)
    (u w : M.native.carrier ()) (ha : M.native.denote v a = {u})
    (hb : M.native.denote v b = {w}) (x : M.native.carrier ()) :
    x ∈ M.native.denote v (equal a b) ↔ u = w := by
  change (∃ values : Fin 1 → M.native.carrier (),
    (∀ i, values i ∈ M.native.denote v a ∩ M.native.denote v b) ∧
      x ∈ M.native.operation .ceil values) ↔ _
  rw [ha, hb]
  constructor
  · rintro ⟨values, h, _⟩
    exact (h 0).1.symm.trans (h 0).2
  · intro h
    exact ⟨fun _ => u, fun _ => ⟨rfl, h⟩, by rw [M.ceil]; trivial⟩

/-- A constructor applied to object variables denotes its decoded value. -/
theorem constructor_vars_denote {A : Signature} (M : Model A) {k n : Nat}
    (v : Fin k → M.native.carrier ()) (op : A.Op n) (indices : Fin n → Fin k) :
    M.native.denote v (.app (.constructor op) (fun i => .var (indices i)) : Raw A k) =
      {M.decode.op (w := fun _ => ()) (s := ()) op (fun i => v (indices i))} := by
  ext x
  constructor
  · rintro ⟨args, hargs, hop⟩
    have he : args = fun i => v (indices i) := funext hargs
    subst args
    exact (M.constructor_mem_iff _ _ _).1 hop
  · intro hx
    exact ⟨fun i => v (indices i), fun _ => rfl, (M.constructor_mem_iff _ _ _).2 hx⟩

/-- Closing the object context quantifies every valuation, independently of the result. -/
theorem closeAll_mem {A : Signature} (M : Model A) {r : Nat}
    (η : Fin r → Set (M.native.carrier ())) (x : M.native.carrier ()) :
    ∀ k (p : Pat A r k) (v0 : Fin 0 → M.native.carrier ()),
      x ∈ (closeAll k p).denote M.native v0 η ↔
        ∀ v : Fin k → M.native.carrier (), x ∈ p.denote M.native v η := by
  intro k
  induction k with
  | zero =>
    intro p v0
    constructor
    · intro h v
      have hv : v = v0 := funext fun i => i.elim0
      simpa only [hv, closeAll] using h
    · intro h
      exact h v0
  | succ k ih =>
    show ∀ (p : Pat A r (k + 1)) (v0 : Fin 0 → M.native.carrier ()),
      x ∈ (closeAll (k + 1) p).denote M.native v0 η ↔
        ∀ v : Fin (k + 1) → M.native.carrier (), x ∈ p.denote M.native v η
    intro p v0
    rw [closeAll, ih]
    change (∀ v : Fin k → M.native.carrier (), ∀ a, x ∈ p.denote M.native (Fin.cases a v) η) ↔ _
    constructor
    · intro h v
      have hv : Fin.cases (v 0) (fun i => v i.succ) = v := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simpa only [hv, closeAll] using h (fun i => v i.succ) (v 0)
    · intro h v a
      exact h (Fin.cases a v)

theorem disjointClause_mem {B : Signature} (p : Constraint B) (M : Model B)
    (c d : Fin p.constructors.count) (hcd : c ≠ d) (x : M.native.carrier ()) :
    x ∈ (disjointClause p c d).denote M.native Fin.elim0 Fin.elim0 ↔
      ∀ (xs : Fin (p.constructors.arity c) → M.native.carrier ())
        (ys : Fin (p.constructors.arity d) → M.native.carrier ()),
        M.decode.op (w := fun _ => ()) (s := ()) (p.operation c) xs ≠ M.decode.op (w := fun _ => ()) (s := ()) (p.operation d) ys := by
  simp only [disjointClause, hcd, ↓reduceIte]
  rw [closeAll_mem]
  have he (v : Fin (p.constructors.arity c + p.constructors.arity d) → M.native.carrier ()) :
      x ∈ M.native.denote v (equal (constructorLeft p c d) (constructorRight p c d)) ↔
        M.decode.op (p.operation c) (fun i => v (Fin.castAdd _ i)) =
          M.decode.op (p.operation d) (fun i => v (Fin.natAdd _ i)) :=
    equal_mem M v _ _ _ _ (constructor_vars_denote M v _ _) (constructor_vars_denote M v _ _) x
  change (∀ v, ¬ x ∈ M.native.denote v (equal (constructorLeft p c d) (constructorRight p c d))) ↔ _
  simp_rw [he]
  constructor
  · intro h xs ys
    simpa only [Fin.addCases_left, Fin.addCases_right] using h (Fin.addCases xs ys)
  · intro h v
    exact h _ _

theorem injectiveClause_mem {B : Signature} (p : Constraint B) (M : Model B)
    (c : Fin p.constructors.count) (i : Fin (p.constructors.arity c)) (x : M.native.carrier ()) :
    x ∈ (injectiveClause p c i).denote M.native Fin.elim0 Fin.elim0 ↔
      ∀ (xs ys : Fin (p.constructors.arity c) → M.native.carrier ()),
        M.decode.op (w := fun _ => ()) (s := ()) (p.operation c) xs = M.decode.op (p.operation c) ys → xs i = ys i := by
  rw [injectiveClause, closeAll_mem]
  have ha (v : Fin (p.constructors.arity c + p.constructors.arity c) → M.native.carrier ()) :
      x ∈ M.native.denote v (equal (constructorLeft p c c) (constructorRight p c c)) ↔
        M.decode.op (p.operation c) (fun j => v (Fin.castAdd _ j)) =
          M.decode.op (p.operation c) (fun j => v (Fin.natAdd _ j)) :=
    equal_mem M v _ _ _ _ (constructor_vars_denote M v _ _) (constructor_vars_denote M v _ _) x
  have hb (v : Fin (p.constructors.arity c + p.constructors.arity c) → M.native.carrier ()) :
      x ∈ M.native.denote v (equal (.var (Fin.castAdd _ i)) (.var (Fin.natAdd _ i))) ↔
        v (Fin.castAdd _ i) = v (Fin.natAdd _ i) :=
    equal_mem M v _ _ _ _ rfl rfl x
  change (∀ v, ¬ (x ∈ M.native.denote v (equal (constructorLeft p c c) (constructorRight p c c)) ∧
    ¬ x ∈ M.native.denote v (equal (.var (Fin.castAdd _ i)) (.var (Fin.natAdd _ i))))) ↔ _
  simp_rw [ha, hb, not_and, not_not]
  constructor
  · intro h xs ys he
    have hh : M.decode.op (w := fun _ => ()) (s := ()) (p.operation c) xs = M.decode.op (p.operation c) ys → xs i = ys i := by
      simpa only [Fin.addCases_left, Fin.addCases_right] using h (Fin.addCases xs ys)
    exact hh he
  · intro h v
    exact h _ _

/-- The syntactic finite conjunction checks all actual constructor pairs and arguments. -/
theorem noConfusion_mem {B : Signature} (p : Constraint B) (M : Model B) (x : M.native.carrier ()) :
    x ∈ (noConfusion p).denote M.native Fin.elim0 Fin.elim0 ↔ NoConfusion p M.decode := by
  rw [noConfusion, conjunction_mem]
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_map]
  constructor
  · intro h
    constructor
    · intro c xs ys he
      funext i
      exact (injectiveClause_mem p M c i x).1
        (h _ ⟨c, Or.inr ⟨i, rfl⟩⟩) xs ys he
    · intro c d hcd xs ys
      exact (disjointClause_mem p M c d hcd x).1
        (h _ ⟨c, Or.inl ⟨d, rfl⟩⟩) xs ys
  · rintro ⟨hi, hd⟩ q ⟨c, hq⟩
    rcases hq with ⟨d, rfl⟩ | ⟨i, rfl⟩
    · by_cases hcd : c = d
      · simp only [disjointClause, hcd, ↓reduceIte, top_denote, Set.mem_univ]
      · exact (disjointClause_mem p M c d hcd x).2 (hd c d hcd)
    · exact (injectiveClause_mem p M c i x).2 (fun xs ys he => congrFun (hi c he) i)

/-- The finite native constructor disjunction is the actual algebraic closure operator. -/
theorem generatedBody_mem {B : Signature} (p : Constraint B) (M : Model B)
    (X : Set (M.native.carrier ())) (x : M.native.carrier ()) :
    x ∈ (generatedBody p).denote M.native Fin.elim0 (Fin.cases X Fin.elim0) ↔
      ∃ c args, (∀ i, args i ∈ X) ∧ x = M.decode.op (p.operation c) args := by
  rw [generatedBody, disjunction_mem]
  constructor
  · rintro ⟨q, hq, hx⟩
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨args, hargs, hop⟩ := hx
    exact ⟨c, args, hargs, (M.constructor_mem_iff _ _ _).1 hop⟩
  · rintro ⟨c, args, hargs, hop⟩
    refine ⟨_, List.mem_map.mpr ⟨c, List.mem_finRange c, rfl⟩, ?_⟩
    exact ⟨args, hargs, (M.constructor_mem_iff _ _ _).2 hop⟩

/-- The native least fixed point contains exactly finite constructor evaluations. -/
theorem generated_denote {B : Signature} (p : Constraint B) (M : Model B) :
    (generated p).denote M.native Fin.elim0 Fin.elim0 = Set.range (Tree.eval p M.decode) := by
  apply Set.Subset.antisymm
  · apply Silmaril.Logic.Matching.FixedPoint.mu_induction
    intro x hx
    obtain ⟨c, args, hargs, hx⟩ := (generatedBody_mem p M _ x).1 hx
    choose trees htrees using hargs
    exact ⟨.node c trees, by simpa only [Tree.eval, htrees] using hx.symm⟩
  · rintro x ⟨t, rfl⟩
    induction t with
    | node c args ih =>
      rw [generated, Silmaril.Logic.Matching.FixedPoint.mu_unfold]
      apply (generatedBody_mem p M _ _).2
      exact ⟨c, fun i => Tree.eval p M.decode (args i), ih, rfl⟩

/-- Native satisfaction is exactly actual generatedness and no confusion. -/
theorem compile_satisfies_iff {B : Signature} (p : Constraint B) (M : Model B) :
    Silmaril.Logic.Matching.FixedPoint.Sentence.Satisfies M.native (compile p) ↔
      Generated p M.decode ∧ NoConfusion p M.decode := by
  change (∀ (v : Fin 0 → M.native.carrier ()) (η : Fin 0 → Set (M.native.carrier ())) x,
    x ∈ (generated p).denote M.native v η ∧ x ∈ (noConfusion p).denote M.native v η) ↔ _
  constructor
  · intro h
    constructor
    · intro x
      have hx : x ∈ (generated p).denote M.native Fin.elim0 Fin.elim0 :=
        (h Fin.elim0 Fin.elim0 x).1
      simpa only [generated_denote, Set.mem_range] using hx
    · let x := Classical.choice (M.native.nonempty ())
      exact (noConfusion_mem p M x).1 (h Fin.elim0 Fin.elim0 x).2
  · show Generated p M.decode ∧ NoConfusion p M.decode →
      ∀ (v : Fin 0 → M.native.carrier ()) (η : Fin 0 → Set (M.native.carrier ())) x,
        x ∈ (generated p).denote M.native v η ∧ x ∈ (noConfusion p).denote M.native v η
    rintro ⟨hg, hn⟩ v η x
    have hv : v = Fin.elim0 := funext fun i => i.elim0
    have hη : η = Fin.elim0 := funext fun i => i.elim0
    have hgen : x ∈ (generated p).denote M.native Fin.elim0 Fin.elim0 := by
      rw [generated_denote]
      exact hg x
    have hno : x ∈ (noConfusion p).denote M.native Fin.elim0 Fin.elim0 :=
      (noConfusion_mem p M x).2 hn
    simpa only [hv, hη] using And.intro hgen hno

/-- The target checks the existing source freeness constraint, without assuming it. -/
theorem compile_actual_iff {B : Signature} (p : Constraint B) (M : Model B) :
    Silmaril.Logic.Matching.FixedPoint.Sentence.Satisfies M.native (compile p) ↔
      Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational M.decode p.actual :=
  (compile_satisfies_iff p M).trans
    ((bijective_iff_generated_noConfusion p M.decode).symm.trans (actual_iff_fold_bijective p M.decode).symm)

end Silmaril.Logic.Algebraic.Initial.Matching
