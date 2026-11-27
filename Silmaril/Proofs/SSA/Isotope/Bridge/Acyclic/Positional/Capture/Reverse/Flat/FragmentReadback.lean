module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase

open Positional
open Positional.Capture (Scope)
open SSA.FiniteSum (append)
open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv HasType)
open Positional.Capture.Reverse (CheckedTable)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-! ## Native steps at a case

A case whose scrutinee is a case, a let or a pattern let is natively equal
to that outer construct around the case. These are consequences of the
sequencing laws and case beta at an injection. The bound terms may ask
requests; no purity is used. -/

section Native

variable {n : Nat} {Γ : BoundCtx τ n}

omit [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] in
/-- Weakening beneath the newest slot twice is weakening and then lifting
the weakening under that slot. -/
theorem underBinder_up_proof (K : LetCase.LocallyNameless.Tm Empty Φ (n + 1)) :
    K.underBinder.rename (LetCase.LocallyNameless.Tm.up (Fin.cases 0 (fun i => i.succ.succ))) = K.underBinder.underBinder := by
  simp only [LetCase.LocallyNameless.Tm.underBinder, LetCase.LocallyNameless.Tm.rename_comp]
  exact LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) K

omit [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] in
/-- A case on the newest slot, weakened beneath that slot. -/
theorem case_underBinder_proof (KL KR : LetCase.LocallyNameless.Tm Empty Φ (n + 1)) :
    (LetCase.LocallyNameless.Tm.case (.bv 0) KL.underBinder KR.underBinder).underBinder =
      .case (.bv 0) KL.underBinder.underBinder KR.underBinder.underBinder :=
  congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 0)) (underBinder_up_proof KL) (underBinder_up_proof KR)

/-- A let that binds an injection of a term is natively equal to the
injection: sum eta and case beta at the injection. -/
theorem let_inl_proof (pe : ε) {A B : τ} {a : LetCase.LocallyNameless.Tm Empty Φ n}
    (ha : HasType Φ Γ₀ Γ a A) :
    Equiv pe Γ₀ Γ (.let₁ a (.inl (.bv 0))) (.inl a) (coprod A B) :=
  (Equiv.caseBetaL (pureEff := pe) (A := A) (B := B) (C := coprod A B) ha
    (.inl (.bv (ι := (0 : Fin (n + 1))))) (.inr (.bv (ι := (0 : Fin (n + 1)))))).symm.trans
    (Equiv.caseEta (pureEff := pe) (.inl ha))

theorem let_inr_proof (pe : ε) {A B : τ} {b : LetCase.LocallyNameless.Tm Empty Φ n}
    (hb : HasType Φ Γ₀ Γ b B) :
    Equiv pe Γ₀ Γ (.let₁ b (.inr (.bv 0))) (.inr b) (coprod A B) :=
  (Equiv.caseBetaR (pureEff := pe) (A := A) (B := B) (C := coprod A B) hb
    (.inl (.bv (ι := (0 : Fin (n + 1))))) (.inr (.bv (ι := (0 : Fin (n + 1)))))).symm.trans
    (Equiv.caseEta (pureEff := pe) (.inr hb))

/-- A case on a case of two injections is the inner case with each arm
bound in front of its continuation:

`case (case e (inl a) (inr b)) K₁ K₂ = case e (let₁ a K₁↑) (let₁ b K₂↑)`. -/
theorem case_inj_proof (pe : ε) {Ea Eb A B C : τ} {e : LetCase.LocallyNameless.Tm Empty Φ n}
    {a b KL KR : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (he : HasType Φ Γ₀ Γ e (coprod Ea Eb)) (ha : HasType Φ Γ₀ (Γ.snoc Ea) a A)
    (hb : HasType Φ Γ₀ (Γ.snoc Eb) b B) (hL : HasType Φ Γ₀ (Γ.snoc A) KL C)
    (hR : HasType Φ Γ₀ (Γ.snoc B) KR C) :
    Equiv pe Γ₀ Γ (.case (.case e (.inl a) (.inr b)) KL KR)
      (.case e (.let₁ a KL.underBinder) (.let₁ b KR.underBinder)) C := by
  have hW : HasType Φ Γ₀ (Γ.snoc (coprod A B)) (.case (.bv 0) KL.underBinder KR.underBinder) C :=
    .case (.bv (ι := (0 : Fin (n + 1)))) hL.underBinder hR.underBinder
  have outer := Equiv.bindCase (pureEff := pe) (HasType.case he (.inl ha) (.inr hb)) hL hR
  have pull := Equiv.bindLetCase (pureEff := pe) he (.inl ha) (.inr hb) hW
  have armL : Equiv pe Γ₀ (Γ.snoc Ea)
      (.let₁ (.inl a) (LetCase.LocallyNameless.Tm.case (.bv 0) KL.underBinder KR.underBinder).underBinder)
      (.let₁ a KL.underBinder) C := by
    rw [case_underBinder_proof]
    exact (Equiv.bindCase (pureEff := pe) (.inl ha) hL.underBinder hR.underBinder).symm.trans
      (Equiv.caseBetaL (pureEff := pe) ha hL.underBinder hR.underBinder)
  have armR : Equiv pe Γ₀ (Γ.snoc Eb)
      (.let₁ (.inr b) (LetCase.LocallyNameless.Tm.case (.bv 0) KL.underBinder KR.underBinder).underBinder)
      (.let₁ b KR.underBinder) C := by
    rw [case_underBinder_proof]
    exact (Equiv.bindCase (pureEff := pe) (.inr hb) hL.underBinder hR.underBinder).symm.trans
      (Equiv.caseBetaR (pureEff := pe) hb hL.underBinder hR.underBinder)
  exact outer.trans (pull.trans (Equiv.case (.refl he) armL armR))

/-- A case on a let is the let around the case. -/
theorem case_let_proof (pe : ε) {X A B C : τ} {v : LetCase.LocallyNameless.Tm Empty Φ n}
    {o KL KR : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (hv : HasType Φ Γ₀ Γ v X) (ho : HasType Φ Γ₀ (Γ.snoc X) o (coprod A B))
    (hL : HasType Φ Γ₀ (Γ.snoc A) KL C) (hR : HasType Φ Γ₀ (Γ.snoc B) KR C) :
    Equiv pe Γ₀ Γ (.case (.let₁ v o) KL KR) (.let₁ v (.case o KL.underBinder KR.underBinder)) C := by
  have hW : HasType Φ Γ₀ (Γ.snoc (coprod A B)) (.case (.bv 0) KL.underBinder KR.underBinder) C :=
    .case (.bv (ι := (0 : Fin (n + 1)))) hL.underBinder hR.underBinder
  have outer := Equiv.bindCase (pureEff := pe) (HasType.let₁ hv ho) hL hR
  have assoc := Equiv.bindLet (pureEff := pe) hv ho hW
  have inner : Equiv pe Γ₀ (Γ.snoc X)
      (.let₁ o (LetCase.LocallyNameless.Tm.case (.bv 0) KL.underBinder KR.underBinder).underBinder)
      (.case o KL.underBinder KR.underBinder) C := by
    rw [case_underBinder_proof]
    exact (Equiv.bindCase (pureEff := pe) ho hL.underBinder hR.underBinder).symm
  exact outer.trans (assoc.trans (Equiv.let₁ (.refl hv) inner))

/-- A case on a pattern let is the pattern let around the case. -/
theorem case_let₂_proof (pe : ε) {X Y A B C : τ} {v : LetCase.LocallyNameless.Tm Empty Φ n}
    {o : LetCase.LocallyNameless.Tm Empty Φ (n + 2)}
    {KL KR : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} (hv : HasType Φ Γ₀ Γ v (product X Y))
    (ho : HasType Φ Γ₀ ((Γ.snoc X).snoc Y) o (coprod A B)) (hL : HasType Φ Γ₀ (Γ.snoc A) KL C)
    (hR : HasType Φ Γ₀ (Γ.snoc B) KR C) :
    Equiv pe Γ₀ Γ (.case (.let₂ v o) KL KR)
      (.let₂ v (.case o KL.underBinder.underBinder KR.underBinder.underBinder)) C := by
  have hW : HasType Φ Γ₀ (Γ.snoc (coprod A B)) (.case (.bv 0) KL.underBinder KR.underBinder) C :=
    .case (.bv (ι := (0 : Fin (n + 1)))) hL.underBinder hR.underBinder
  have outer := Equiv.bindCase (pureEff := pe) (HasType.let₂ hv ho) hL hR
  have assoc := Equiv.bindLetPair (pureEff := pe) hv ho hW
  have inner : Equiv pe Γ₀ ((Γ.snoc X).snoc Y)
      (.let₁ o (LetCase.LocallyNameless.Tm.case (.bv 0) KL.underBinder KR.underBinder).underBinder.underBinder)
      (.case o KL.underBinder.underBinder KR.underBinder.underBinder) C := by
    rw [case_underBinder_proof, case_underBinder_proof]
    exact (Equiv.bindCase (pureEff := pe) ho hL.underBinder.underBinder hR.underBinder.underBinder).symm
  exact outer.trans (assoc.trans (Equiv.let₂ (.refl hv) inner))

end Native

/-! ## Exit tags and continuations as terms -/

section Terms

variable {n : Nat}

/-- The injections of the exit at a position, around a term. -/
def tagTm : Nat → LetCase.LocallyNameless.Tm Empty Φ n → LetCase.LocallyNameless.Tm Empty Φ n
  | 0, a => .inl a
  | i + 1, a => .inr (tagTm i a)

omit [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] in
theorem tagTm_rename {m : Nat} (f : Fin n → Fin m) : (i : Nat) →
    (a : LetCase.LocallyNameless.Tm Empty Φ n) →
    (tagTm i a).rename f = tagTm i (a.rename f)
  | 0, _ => rfl
  | i + 1, a => congrArg LetCase.LocallyNameless.Tm.inr (tagTm_rename f i a)

omit [HasEff Φ ε] in
/-- The term of a tagged operand. -/
theorem tag_fst : (L : LCtx τ) → (i : Nat) → {A : τ} → (hi : At L i A) → {β : BoundCtx τ n} →
    (a : Operand Φ β A) → (FiniteExit.tag L i hi a).1 = tagTm i a.1
  | [], _, _, hi, _, _ => nomatch hi
  | B :: _, 0, A, hi, _, a => by
    obtain rfl : B = A := Option.some.inj hi
    rfl
  | _ :: L, i + 1, _, hi, _, a => congrArg LetCase.LocallyNameless.Tm.inr (tag_fst L i hi a)

omit [HasEff Φ ε] in
/-- The injections of an exit around a typed term are typed at the packed
exits. -/
theorem tagTm_typed : (L : LCtx τ) → (i : Nat) → {A : τ} → (hi : At L i A) → {β : BoundCtx τ n} →
    {a : LetCase.LocallyNameless.Tm Empty Φ n} → HasType Φ Γ₀ β a A → HasType Φ Γ₀ β (tagTm i a) (packedExitType L)
  | [], _, _, hi, _, _, _ => nomatch hi
  | B :: _, 0, A, hi, _, _, ha => by
    obtain rfl : B = A := Option.some.inj hi
    exact .inl ha
  | _ :: L, i + 1, _, hi, _, _, ha => .inr (tagTm_typed L i hi ha)

/-- A let that binds a term in front of the injections of an exit around
the bound slot is the injections around the term. -/
theorem tag_let_proof (pe : ε) : (L : LCtx τ) → (i : Nat) → {A : τ} → (hi : At L i A) →
    {β : BoundCtx τ n} → {a : LetCase.LocallyNameless.Tm Empty Φ n} → HasType Φ Γ₀ β a A →
    Equiv pe Γ₀ β (.let₁ a (tagTm i (.bv 0))) (tagTm i a) (packedExitType L)
  | [], _, _, hi, _, _, _ => nomatch hi
  | B :: _, 0, A, hi, _, _, ha => by
    obtain rfl : B = A := Option.some.inj hi
    exact let_inl_proof pe ha
  | B :: L, i + 1, A, hi, β, a, ha => by
    have t0 : HasType Φ Γ₀ (β.snoc A) (tagTm i (.bv 0)) (packedExitType L) :=
      tagTm_typed L i hi (.bv (ι := (0 : Fin (n + 1))))
    have ih := tag_let_proof pe L i hi ha
    have inner : Equiv pe Γ₀ (β.snoc A) (.let₁ (tagTm i (.bv 0)) (.inr (.bv 0))) (.inr (tagTm i (.bv 0)))
        (coprod B (packedExitType L)) := let_inr_proof pe t0
    have assoc := Equiv.bindLet (pureEff := pe) ha t0
      (HasType.inr (A := B) (.bv (ι := (0 : Fin (n + 1)))) : HasType Φ Γ₀ (β.snoc (packedExitType L))
        (.inr (.bv 0)) (coprod B (packedExitType L)))
    exact (Equiv.let₁ (.refl ha) inner.symm).trans (assoc.symm.trans
      ((Equiv.let₁ ih (.refl (HasType.inr (A := B) (.bv (ι := (0 : Fin (n + 1))))))).trans
        (let_inr_proof pe (tagTm_typed L i hi ha))))

end Terms

/-! ## The flat compiler on a row

The flat compile of a line is its folded operand bound in front of the
continuation of its label, and the flat compile of a fork is the case on
its folded operand around the continuations of its two labels. The
statements are under any renaming of the context of the body, for any
total vector of continuations of the blocks. -/

section Rows

variable {blocks exits n : Nat} {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}

local notation "Result" => packedExitType (List.ofFn D)

/-- The continuation of a label as a term over a context with the packet
newest: the continuation of a block, weakened along the given map of the
captured context, or the injections of an exit around the packet. -/
def contTm (F : ∀ j, Operand Φ (β.snoc (R j)) Result) {k : Nat} (f : Fin n → Fin k)
    (i : Fin (blocks + exits)) : LetCase.LocallyNameless.Tm Empty Φ (k + 1) :=
  Fin.addCases (fun j => (F j).1.rename (LetCase.LocallyNameless.Tm.up f)) (fun e => tagTm e.val (.bv 0)) i

omit [HasEff Φ ε] in
theorem contTm_typed (F : ∀ j, Operand Φ (β.snoc (R j)) Result) {k : Nat} {δ : BoundCtx τ k}
    (σ : BoundCtx.Renaming β δ) (i : Fin (blocks + exits)) :
    HasType Φ Γ₀ (δ.snoc (append R D i)) (contTm F σ.toFun i) Result := by
  induction i using Fin.addCases with
  | left j =>
    simp only [contTm, Fin.addCases_left, SSA.FiniteSum.append_left]
    exact HasType.rename (σ.up (R j)) (F j).2.toHasType
  | right e =>
    simp only [contTm, Fin.addCases_right, SSA.FiniteSum.append_right]
    exact tagTm_typed (List.ofFn D) e.val (SSA.FiniteSum.at_ofFn D e) (.bv (ι := (0 : Fin (k + 1))))

omit [HasEff Φ ε] in
/-- Weakening a continuation beneath its packet is the continuation along
the weakened map. -/
theorem contTm_underBinder (F : ∀ j, Operand Φ (β.snoc (R j)) Result) {k : Nat} (f : Fin n → Fin k)
    (i : Fin (blocks + exits)) :
    (contTm F f i).underBinder = contTm F (fun x => (f x).succ) i := by
  induction i using Fin.addCases with
  | left j =>
    simp only [contTm, Fin.addCases_left, LetCase.LocallyNameless.Tm.underBinder, LetCase.LocallyNameless.Tm.rename_comp]
    exact LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) (F j).1
  | right e =>
    simp only [contTm, Fin.addCases_right, LetCase.LocallyNameless.Tm.underBinder]
    exact tagTm_rename _ e.val (.bv 0)

end Rows

section Compile

variable {blocks exits n : Nat} {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}

local notation "Result" => packedExitType (List.ofFn D)

omit [HasEff Φ ε] in
/-- The term of an operand does not change when its type is rewritten. -/
theorem operand_cast_fst {m : Nat} {γ : BoundCtx τ m} {A B : τ} (h : A = B) (a : Operand Φ γ A) :
    (h ▸ a : Operand Φ γ B).1 = a.1 := by
  subst h
  rfl

omit [HasEff Φ ε] in
/-- The term of a flat jump to a block: the argument bound in front of the
continuation. -/
theorem compileJump_left_fst {m : Nat} {γ : BoundCtx τ m} (j : Fin blocks)
    (a : Operand Φ γ (append R D (j.castAdd exits)))
    (next : ∀ j' (_ : j.castAdd exits = j'.castAdd exits), Code Φ (γ.snoc (R j')) Result) :
    (compileJump (j.castAdd exits) a next).toLetCase.1 = .let₁ a.1 (next j rfl).toLetCase.1 := by
  simp only [compileJump, Fin.addCases_left, Code.toLetCase]
  exact congrArg (fun x => LetCase.LocallyNameless.Tm.let₁ x (next j rfl).toLetCase.1) (operand_cast_fst _ a)

omit [HasEff Φ ε] in
/-- The term of a flat jump to an exit: the injections of the exit around
the argument. -/
theorem compileJump_right_fst {m : Nat} {γ : BoundCtx τ m} (e : Fin exits)
    (a : Operand Φ γ (append R D (e.natAdd blocks)))
    (next : ∀ j' (_ : e.natAdd blocks = j'.castAdd exits), Code Φ (γ.snoc (R j')) Result) :
    (compileJump (e.natAdd blocks) a next).toLetCase.1 = tagTm e.val a.1 := by
  simp only [compileJump, Fin.addCases_right, Code.toLetCase]
  exact (tag_fst _ _ _ _).trans (congrArg (tagTm e.val) (operand_cast_fst _ a))

/-- A flat jump, under a renaming of its context: the renamed argument
bound in front of the continuation of the label. -/
theorem jump_compile_proof (pe : ε) (F : ∀ j, Operand Φ (β.snoc (R j)) Result) {m : Nat}
    {γ : BoundCtx τ m} (sc : Scope β γ) (i : Fin (blocks + exits))
    (a : Operand Φ γ (append R D i)) {k : Nat} {δ : BoundCtx τ k} (ρ : BoundCtx.Renaming γ δ) :
    Equiv pe Γ₀ δ
      ((compileJump i a (fun j _ => Code.br (weakenPacket sc (F j)))).toLetCase.1.rename ρ.toFun)
      (.let₁ (a.1.rename ρ.toFun) (contTm F (fun x => ρ.toFun (sc.renaming.toFun x)) i)) Result := by
  have typed := HasType.rename ρ
    (compileJump i a (fun j _ => Code.br (weakenPacket sc (F j)))).toLetCase.2.toHasType
  induction i using Fin.addCases with
  | left j =>
    have same : (compileJump (j.castAdd exits) a
          (fun j _ => Code.br (weakenPacket sc (F j)))).toLetCase.1.rename ρ.toFun =
        .let₁ (a.1.rename ρ.toFun)
          (contTm F (fun x => ρ.toFun (sc.renaming.toFun x)) (j.castAdd exits)) := by
      rw [compileJump_left_fst]
      simp only [contTm, Fin.addCases_left]
      exact congrArg (LetCase.LocallyNameless.Tm.let₁ (a.1.rename ρ.toFun))
        ((LetCase.LocallyNameless.Tm.rename_comp _ _ (F j).1).trans
          (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) (F j).1))
    exact same ▸ .refl typed
  | right e =>
    have retype : ∀ t : LetCase.LocallyNameless.Tm Empty Φ k, HasType Φ Γ₀ δ t (append R D (e.natAdd blocks)) →
        HasType Φ Γ₀ δ t (D e) := fun t h => by rwa [SSA.FiniteSum.append_right] at h
    have ha : HasType Φ Γ₀ δ (a.1.rename ρ.toFun) (D e) := retype _ (HasType.rename ρ a.2.toHasType)
    have same : (compileJump (e.natAdd blocks) a
          (fun j _ => Code.br (weakenPacket sc (F j)))).toLetCase.1.rename ρ.toFun =
        tagTm e.val (a.1.rename ρ.toFun) := by
      rw [compileJump_right_fst]
      exact tagTm_rename ρ.toFun e.val a.1
    rw [same]
    simp only [contTm, Fin.addCases_right]
    exact (tag_let_proof pe (List.ofFn D) e.val (SSA.FiniteSum.at_ofFn D e) ha).symm

/-- The flat compile of a line, under a renaming of its context: the
renamed folded operand bound in front of the continuation of its label. -/
theorem line_compile_proof (pe : ε) (F : ∀ j, Operand Φ (β.snoc (R j)) Result) : {m : Nat} →
    {γ : BoundCtx τ m} → {t : Flat Φ (blocks + exits) m} →
    (b : Body Φ (append R D) γ t) → ∀ r, b.line = some r → (sc : Scope β γ) → {k : Nat} →
    {δ : BoundCtx τ k} → (ρ : BoundCtx.Renaming γ δ) →
    Equiv pe Γ₀ δ ((compileBody b sc (fun j _ => F j)).toLetCase.1.rename ρ.toFun)
      (.let₁ (r.2.1.rename ρ.toFun) (contTm F (fun x => ρ.toFun (sc.renaming.toFun x)) r.1)) Result
  | _, _, _, .br i a, r, h, sc, _, _, ρ => by
    cases h
    exact jump_compile_proof pe F sc i a ρ
  | _, _, _, .let₁ (A := X) v tail, r, h, sc, _, δ, ρ => by
    simp only [Body.line, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have ih := line_compile_proof pe F tail r' hr' (.skip sc X) (ρ.up X)
    have hv := HasType.rename ρ v.2.toHasType
    have ha := HasType.rename (ρ.up X) r'.2.2.toHasType
    have assoc := Equiv.bindLet (pureEff := pe) hv ha
      (contTm_typed F (sc.renaming.comp ρ) r'.1)
    rw [contTm_underBinder] at assoc
    exact (Equiv.let₁ (.refl hv) ih).trans assoc.symm
  | _, _, _, .let₂ (A := X) (B := Y) v tail, r, h, sc, _, δ, ρ => by
    simp only [Body.line, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have ih := line_compile_proof pe F tail r' hr' (.skip (.skip sc X) Y) ((ρ.up X).up Y)
    have hv := HasType.rename ρ v.2.toHasType
    have ha := HasType.rename ((ρ.up X).up Y) r'.2.2.toHasType
    have assoc := Equiv.bindLetPair (pureEff := pe) hv ha
      (contTm_typed F (sc.renaming.comp ρ) r'.1)
    rw [contTm_underBinder, contTm_underBinder] at assoc
    exact (Equiv.let₂ (.refl hv) ih).trans assoc.symm
  | _, _, _, .case _ _ _, r, h, _, _, _, _ => by
    simp [Body.line] at h

/-- The flat compile of a fork, under a renaming of its context: the case
on the renamed folded operand around the continuations of its two labels. -/
theorem fork_compile_proof (pe : ε) (F : ∀ j, Operand Φ (β.snoc (R j)) Result) : {m : Nat} →
    {γ : BoundCtx τ m} → {t : Flat Φ (blocks + exits) m} →
    (b : Body Φ (append R D) γ t) → ∀ r, b.fork = some r → (sc : Scope β γ) → {k : Nat} →
    {δ : BoundCtx τ k} → (ρ : BoundCtx.Renaming γ δ) →
    Equiv pe Γ₀ δ ((compileBody b sc (fun j _ => F j)).toLetCase.1.rename ρ.toFun)
      (.case (r.2.2.1.rename ρ.toFun) (contTm F (fun x => ρ.toFun (sc.renaming.toFun x)) r.1)
        (contTm F (fun x => ρ.toFun (sc.renaming.toFun x)) r.2.1)) Result
  | _, _, _, .br _ _, r, h, _, _, _, _ => by
    simp [Body.fork] at h
  | _, _, _, .let₁ (A := X) v tail, r, h, sc, _, δ, ρ => by
    simp only [Body.fork, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have ih := fork_compile_proof pe F tail r' hr' (.skip sc X) (ρ.up X)
    have hv := HasType.rename ρ v.2.toHasType
    have ho := HasType.rename (ρ.up X) r'.2.2.2.toHasType
    have step := case_let_proof pe hv ho (contTm_typed F (sc.renaming.comp ρ) r'.1)
      (contTm_typed F (sc.renaming.comp ρ) r'.2.1)
    rw [contTm_underBinder, contTm_underBinder] at step
    exact (Equiv.let₁ (.refl hv) ih).trans step.symm
  | _, _, _, .let₂ (A := X) (B := Y) v tail, r, h, sc, _, δ, ρ => by
    simp only [Body.fork, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have ih := fork_compile_proof pe F tail r' hr' (.skip (.skip sc X) Y) ((ρ.up X).up Y)
    have hv := HasType.rename ρ v.2.toHasType
    have ho := HasType.rename ((ρ.up X).up Y) r'.2.2.2.toHasType
    have step := case_let₂_proof pe hv ho (contTm_typed F (sc.renaming.comp ρ) r'.1)
      (contTm_typed F (sc.renaming.comp ρ) r'.2.1)
    rw [contTm_underBinder, contTm_underBinder, contTm_underBinder, contTm_underBinder] at step
    exact (Equiv.let₂ (.refl hv) ih).trans step.symm
  | _, _, _, .case (A := Ea) (B := Eb) e left right, r, h, sc, _, δ, ρ => by
    simp only [Body.fork, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, r', hr', rfl⟩ := h
    have ihl := line_compile_proof pe F left l hl (.skip sc Ea) (ρ.up Ea)
    have ihr := line_compile_proof pe F right r' hr' (.skip sc Eb) (ρ.up Eb)
    have he := HasType.rename ρ e.2.toHasType
    have ha := HasType.rename (ρ.up Ea) l.2.2.toHasType
    have hb := HasType.rename (ρ.up Eb) r'.2.2.toHasType
    have step := case_inj_proof pe he ha hb (contTm_typed F (sc.renaming.comp ρ) l.1)
      (contTm_typed F (sc.renaming.comp ρ) r'.1)
    rw [contTm_underBinder, contTm_underBinder] at step
    exact (Equiv.case (.refl he) ihl ihr).trans step.symm

end Compile

/-! ## The table compiler on a row

The table compile of a target is the continuation of its label, when the
continuations of the blocks agree at every scope. So the flat compile of a
block and the table compile of its row are natively equal. -/

section Simulation

variable {blocks exits n : Nat} {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}

local notation "Result" => packedExitType (List.ofFn D)

omit [HasEff Φ ε] in
/-- The term of the table compile of a target that is a block. -/
theorem target_local_fst {A : τ} (t : Positional.Capture.Target R (List.ofFn D) A) (j : Fin blocks)
    (eq : R j = A) (is : t = cast (congrArg (Positional.Capture.Target R (List.ofFn D)) eq) (.local j))
    {labels : List (Fin blocks)} (edge : ∀ j' ∈ t.locals, j' ∈ labels) (mem : j ∈ t.locals)
    {k : Nat} {γ : BoundCtx τ k} (s : Scope β γ)
    (next : Positional.Capture.LocalContinuations β R (List.ofFn D) Φ labels) :
    (t.compile edge s next).encode.toLetCase.1 = (next j (edge j mem) s).encode.toLetCase.1 := by
  subst eq
  subst is
  rfl

omit [HasEff Φ ε] in
/-- The term of the table compile of a target that is an exit. -/
theorem target_exit_fst {A : τ} (t : Positional.Capture.Target R (List.ofFn D) A) {e : Nat}
    (at_ : At (List.ofFn D) e A) (is : t = .exit at_) {labels : List (Fin blocks)}
    (edge : ∀ j' ∈ t.locals, j' ∈ labels) {k : Nat} {γ : BoundCtx τ k} (s : Scope β γ)
    (next : Positional.Capture.LocalContinuations β R (List.ofFn D) Φ labels) :
    (t.compile edge s next).encode.toLetCase.1 = tagTm e (.bv 0) := by
  subst is
  exact tag_fst (List.ofFn D) e at_ _

/-- The continuation of a label is natively equal to the table compile of
the target of the label, when the continuations of the blocks agree with
the table continuations at every scope. -/
theorem target_cont_proof (pe : ε) (F : ∀ j, Operand Φ (β.snoc (R j)) Result)
    (i : Fin (blocks + exits))
    {labels : List (Fin blocks)} (edge : ∀ j ∈ (labelTarget R D i).locals, j ∈ labels) {k : Nat}
    {γ : BoundCtx τ k} (s : Scope β γ)
    (next : Positional.Capture.LocalContinuations β R (List.ofFn D) Φ labels)
    (agree : ∀ j (hj : j ∈ labels) {k' : Nat} {γ' : BoundCtx τ k'} (s' : Scope β γ'),
      Equiv pe Γ₀ (γ'.snoc (R j)) ((F j).1.rename (LetCase.LocallyNameless.Tm.up s'.renaming.toFun))
        (next j hj s').encode.toLetCase.1 Result) :
    Equiv pe Γ₀ (γ.snoc (append R D i)) (contTm F s.renaming.toFun i)
      ((labelTarget R D i).compile edge s next).encode.toLetCase.1 Result := by
  induction i using Fin.addCases with
  | left j =>
    have mem : j ∈ (labelTarget R D (j.castAdd exits)).locals := by
      rw [labelTarget_locals_proof]
      simp only [Fin.addCases_left, List.mem_singleton]
    have term := target_local_fst (labelTarget R D (j.castAdd exits)) j
      (SSA.FiniteSum.append_left R D j).symm (by simp only [labelTarget, Fin.addCases_left]) edge mem s next
    have retype : ∀ x y : LetCase.LocallyNameless.Tm Empty Φ (k + 1), Equiv pe Γ₀ (γ.snoc (R j)) x y Result →
        Equiv pe Γ₀ (γ.snoc (append R D (j.castAdd exits))) x y Result := fun x y h => by
      rw [SSA.FiniteSum.append_left]
      exact h
    rw [term]
    simp only [contTm, Fin.addCases_left]
    exact retype _ _ (agree j (edge j mem) s)
  | right e =>
    have term := target_exit_fst (labelTarget R D (e.natAdd blocks))
      ((SSA.FiniteSum.at_ofFn D e).trans (congrArg some (SSA.FiniteSum.append_right R D e).symm))
      (by simp only [labelTarget, Fin.addCases_right]) edge s next
    have typed := contTm_typed F s.renaming (e.natAdd blocks)
    rw [term]
    simp only [contTm, Fin.addCases_right] at typed ⊢
    exact .refl typed

/-- The row simulation. The flat compile of a block, weakened along a
scope, is natively equal to the table compile of its row at that scope,
for any vector of flat continuations and any table continuations that
agree with it at every scope. -/
theorem row_compile_proof (pe : ε) (F : ∀ j, Operand Φ (β.snoc (R j)) Result) {P : τ}
    {t : Flat Φ (blocks + exits) (n + 1)} (b : Body Φ (append R D) (β.snoc P) t)
    (row : Positional.Capture.Block Φ β R (List.ofFn D) P) (h : b.row = some row) {k : Nat}
    {γ : BoundCtx τ k} (s : Scope β γ)
    (next : Positional.Capture.LocalContinuations β R (List.ofFn D) Φ row.locals)
    (agree : ∀ j (hj : j ∈ row.locals) {k' : Nat} {γ' : BoundCtx τ k'} (s' : Scope β γ'),
      Equiv pe Γ₀ (γ'.snoc (R j)) ((F j).1.rename (LetCase.LocallyNameless.Tm.up s'.renaming.toFun))
        (next j hj s').encode.toLetCase.1 Result) :
    Equiv pe Γ₀ (γ.snoc P)
      ((compileBody b (.skip .base P) (fun j _ => F j)).toLetCase.1.rename (LetCase.LocallyNameless.Tm.up s.renaming.toFun))
      (row.compile s next).encode.toLetCase.1 Result := by
  unfold Body.row at h
  cases hl : b.line with
  | some r =>
    rw [hl] at h
    cases h
    have line := line_compile_proof pe F b r hl (.skip .base P) (s.renaming.up P)
    have target := target_cont_proof pe F r.1 (fun _ hj => hj) (.skip s P) next agree
    exact line.trans (Equiv.let₁ (.refl (HasType.rename (s.renaming.up P) r.2.2.toHasType)) target)
  | none =>
    rw [hl] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    have fork := fork_compile_proof pe F b r hr (.skip .base P) (s.renaming.up P)
    have left := target_cont_proof pe F r.1 (fun _ hj => List.mem_append_left _ hj) (.skip s P) next agree
    have right := target_cont_proof pe F r.2.1 (fun _ hj => List.mem_append_right _ hj) (.skip s P) next
      agree
    exact fork.trans
      (Equiv.case (.refl (HasType.rename (s.renaming.up P) r.2.2.2.toHasType)) left right)

end Simulation

/-! ## The whole table

The rows are simulated one at a time, in the order of the checked rank of
the table, with the flat compiles of the blocks as the continuation vector.
The entry is a line into the first block. -/

section Global

variable {size exits n : Nat} {β : BoundCtx τ n} {R : Fin (size + 1) → τ} {D : Fin exits → τ}
  {g : FiniteCFG Φ (size + 1) exits n}

local notation "Result" => packedExitType (List.ofFn D)

omit [HasEff Φ ε] in
/-- The flat compile of a block is the compile of its body around the flat
compiles of the blocks. -/
theorem compileAt_fst (w : Witness g β R D) (ranked : Rank.check (localTargets g) = true)
    (i : Fin (size + 1)) :
    (compileAt w ranked i).toLetCase.1 =
      (compileBody (w.block i) (.skip .base (R i))
        (fun j _ => (compileAt w ranked j).toLetCase)).toLetCase.1 := by
  unfold compileAt
  rw [compileRankedAt.eq_def]

omit [HasEff Φ ε] in
/-- The flat compile of a graph is the compile of its entry around the flat
compiles of the blocks. -/
theorem compile_fst (w : Witness g β R D) (ranked : Rank.check (localTargets g) = true) :
    (compile w ranked).toLetCase.1 =
      (compileBody w.entry .base (fun j _ => (compileAt w ranked j).toLetCase)).toLetCase.1 :=
  rfl

/-- The flat compile of a block, weakened along a scope, is natively equal
to the table compile of the block at that scope. By induction on a bound of
the checked rank of the block. -/
theorem block_readback_proof (pe : ε) (w : Witness g β R D) (h : w.Delimited)
    (ranked : Rank.check (localTargets g) = true) (checked : (w.table h).check = true) :
    ∀ (bound : Nat) (i : Fin (size + 1)), (w.table h).rank i < bound → ∀ {k : Nat}
      {γ : BoundCtx τ k} (s : Scope β γ),
      Equiv pe Γ₀ (γ.snoc (R i)) ((compileAt w ranked i).toLetCase.1.rename (LetCase.LocallyNameless.Tm.up s.renaming.toFun))
        ((w.table h).compileAt checked i s).encode.toLetCase.1 Result := by
  intro bound
  induction bound with
  | zero =>
    intro i hi
    omega
  | succ bound ih =>
    intro i hi k γ s
    rw [compileAt_fst, Positional.Capture.Table.compileAt.eq_def]
    exact row_compile_proof pe (fun j => (compileAt w ranked j).toLetCase) (w.block i)
      (((w.block i).row).get (h.rows i)) (Option.some_get (h.rows i)).symm s _
      (fun j hj _ _ s' => ih j (by
        have := (w.table h).decreases checked (i := i) (j := j) hj
        omega) s')

omit [HasEff Φ ε] in
/-- The term of a retyped operand. -/
theorem operand_retype_fst {m : Nat} {γ : BoundCtx τ m} {A B : τ} (eq : A = B) (a : Operand Φ γ A) :
    (cast (congrArg (Operand Φ γ) eq) a).1 = a.1 := by
  subst eq
  rfl

omit [HasEff Φ ε] in
/-- The entry of a graph in the fragment is a line into the first block,
and the entry operand has the term of the operand of the line. -/
theorem entry_line_proof (w : Witness g β R D) (o : Operand Φ β (R 0))
    (ho : w.entryOperand = some o) :
    ∃ a : Operand Φ β (append R D (Fin.castAdd exits 0)),
      w.entry.line = some ⟨Fin.castAdd exits 0, a⟩ ∧ o.1 = a.1 := by
  unfold Witness.entryOperand at ho
  cases hl : w.entry.line with
  | none =>
    rw [hl] at ho
    cases ho
  | some r =>
    obtain ⟨i, a⟩ := r
    rw [hl] at ho
    simp only [Option.bind_some] at ho
    split at ho
    · rename_i hi
      subst hi
      cases ho
      exact ⟨a, rfl, operand_retype_fst (SSA.FiniteSum.append_left R D 0) a⟩
    · cases ho

/-- The readback of the checked table of a graph in the fragment is
natively equal to the flat compile of the graph. -/
theorem checkedTable_readback_proof (pe : ε) (w : Witness g β R D) (h : w.Delimited)
    (ranked : Rank.check (localTargets g) = true) (checked : (w.table h).check = true) :
    Equiv pe Γ₀ β (compile w ranked).toLetCase.1 (w.checkedTable h checked).toLetCase.1 Result := by
  obtain ⟨a, line, term⟩ := entry_line_proof w (w.entryOperand.get h.entry) (Option.some_get h.entry).symm
  have flat := line_compile_proof pe (fun j => (compileAt w ranked j).toLetCase) w.entry _ line .base
    (BoundCtx.Renaming.id β)
  have block := block_readback_proof pe w h ranked checked _ 0 (Nat.lt_succ_self _) .base
  have retype : ∀ x y : LetCase.LocallyNameless.Tm Empty Φ (n + 1), Equiv pe Γ₀ (β.snoc (R 0)) x y Result →
      Equiv pe Γ₀ (β.snoc (append R D (Fin.castAdd exits 0))) x y Result := fun x y e => by
    rw [SSA.FiniteSum.append_left]
    exact e
  have typed : HasType Φ Γ₀ β a.1 (append R D (Fin.castAdd exits 0)) := a.2.toHasType
  rw [compile_fst]
  show Equiv pe Γ₀ β _ (.let₁ (w.entryOperand.get h.entry).1
    ((w.table h).compileAt checked 0 .base).encode.toLetCase.1) Result
  rw [term]
  simp only [contTm, Fin.addCases_left] at flat
  have id_term : ∀ x : LetCase.LocallyNameless.Tm Empty Φ n, x.rename (BoundCtx.Renaming.id β).toFun = x := fun x =>
    LetCase.LocallyNameless.Tm.rename_id x
  rw [id_term, id_term] at flat
  exact flat.trans (Equiv.let₁ (.refl typed) (retype _ _ block))

end Global

end Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase
