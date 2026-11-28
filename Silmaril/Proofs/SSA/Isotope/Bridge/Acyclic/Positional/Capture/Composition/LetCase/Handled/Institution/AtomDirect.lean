module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv HasType Pure)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged Binary

variable {α Φ : Type} {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-! ## A pair slot commutes with a later binding

A pattern let on a pair slot may be moved in front of a let that precedes
it. The pair slot is a variable, so it is pure. The derivation uses native
typed laws only: pure-let beta at the slot and at a pair of variables,
pair eta at the slot, the sequencing law that pulls a pattern let out of
the scrutinee of a let, and pair beta. -/

section Commute

variable [HasTy Φ (Ty α)]

/-- A let followed by a pattern let on an older pair slot is natively
equal to the pattern let followed by the let. The bound term is weakened
past the two components, and the body has its three newest slots moved. -/
theorem let_pair_comm_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {A B X C : Ty α} (j : Fin m)
    (hj : Δ.get j = .product A B) {E : LetCase.LocallyNameless.Tm Empty Φ m} {body : LetCase.LocallyNameless.Tm Empty Φ (m + 3)}
    (hE : HasType Φ Γ₀ Δ E X) (hBody : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B) body C) :
    Equiv false Γ₀ Δ (.let₁ E (.let₂ (.bv j.succ) body))
      (.let₂ (.bv j) (.let₁ (E.rename (fun i => i.succ.succ)) (body.rename afterPair))) C := by
  have hx : HasType Φ Γ₀ Δ (.bv j) (.product A B) := hj ▸ .bv
  -- the body under the pair slot
  let ins := (((BoundCtx.Renaming.succ Δ (.product A B)).up X).up A).up B
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) := .let₁ (E.rename Fin.succ) (.let₂ (.bv 1) (body.rename ins.toFun))
  have hK : HasType Φ Γ₀ (Δ.snoc (.product A B)) K C :=
    .let₁ (HasType.rename (BoundCtx.Renaming.succ Δ (.product A B)) hE)
      (.let₂ (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename ins hBody))
  have enter := Equiv.letBeta (pureEff := false) Pure.bv hx hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv j) = .let₁ E (.let₂ (.bv j.succ) body) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · exact (LetCase.LocallyNameless.Tm.bsubst_congr (fun _ => rfl) E).trans
        (LetCase.LocallyNameless.Tm.bsubst_id E)
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_id body)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at enter
  -- eta-expand the pair slot and pull the pattern let out
  have eta := Equiv.let₁ (Equiv.pairEta (pureEff := false) hx).symm (.refl hK)
  have pull := Equiv.bindLetPair (pureEff := false) hx
    (.pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))) hK
  -- substitute the pair of components for the pair slot
  have hPair : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (.pair (.bv 1) (.bv 0)) (.product A B) :=
    .pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))
  have beta := Equiv.letBeta (pureEff := false) (Pure.pair Pure.bv Pure.bv) hPair hK.underBinder.underBinder
  let past : BoundCtx.Renaming Δ ((Δ.snoc A).snoc B) :=
    (BoundCtx.Renaming.succ Δ A).comp (BoundCtx.Renaming.succ (Δ.snoc A) B)
  let ins2 := ((past.up X).up A).up B
  have beta_eq : LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder (.pair (.bv 1) (.bv 0)) =
      .let₁ (E.rename (fun i => i.succ.succ)) (.let₂ (.pair (.bv 2) (.bv 1)) (body.rename ins2.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · exact (LetCase.LocallyNameless.Tm.bsubst_congr (fun _ => rfl) E).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ E)
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename ins2.toFun body)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [beta_eq] at beta
  -- reduce the pattern let on the pair of components
  have hBody₂ : HasType Φ Γ₀ (((((Δ.snoc A).snoc B).snoc X).snoc A).snoc B) (body.rename ins2.toFun) C :=
    HasType.rename ins2 hBody
  have hA : HasType Φ Γ₀ (((Δ.snoc A).snoc B).snoc X) (.bv 2) A := .bv (ι := (2 : Fin (m + 3)))
  have hB : HasType Φ Γ₀ (((Δ.snoc A).snoc B).snoc X) (.bv 1) B := .bv (ι := (1 : Fin (m + 3)))
  have split := Equiv.pairBeta (pureEff := false) hA hB hBody₂
  have first := Equiv.letBeta (pureEff := false) Pure.bv hA (.let₁ hB.lift hBody₂)
  have first_eq : LetCase.LocallyNameless.Tm.instantiate
      (.let₁ (LetCase.LocallyNameless.Tm.lift (.bv 1)) (body.rename ins2.toFun))
      (.bv (2 : Fin (m + 3))) =
      .let₁ (.bv 1) (LetCase.LocallyNameless.Tm.bsubst
        (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv 2) (fun i => .bv i))) (body.rename ins2.toFun)) := rfl
  rw [first_eq] at first
  obtain ⟨-, typed⟩ := first.hasType
  cases typed with
  | let₁ hV hZ =>
    cases hV
    have second := Equiv.letBeta (pureEff := false) Pure.bv hB hZ
    have second_eq : LetCase.LocallyNameless.Tm.instantiate
        (LetCase.LocallyNameless.Tm.bsubst
          (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv 2) (fun i => .bv i))) (body.rename ins2.toFun))
        (.bv (1 : Fin (m + 3))) = body.rename afterPair := by
      simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_rename,
        LetCase.LocallyNameless.Tm.bsubst_comp]
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename afterPair body)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    rw [second_eq] at second
    have hE'' : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (E.rename (fun i => i.succ.succ)) X :=
      HasType.rename past hE
    exact enter.symm.trans (eta.trans (pull.trans (Equiv.let₂ (.refl hx)
      (beta.trans (Equiv.let₁ (.refl hE'') (split.trans (first.trans second)))))))

end Commute

/-! ## Pattern lets on pair slots commute

Two pattern lets on pair slots may be exchanged, and a pattern let on an
older pair slot may be moved in front of a bound tuple and the pattern lets
that unpack it. These are derived from native typed laws, like the
equation above. -/

section Interchange

variable [HasTy Φ (Ty α)]

/-- A pattern let on a pair of slots is natively equal to its body with the
two components renamed to those slots. -/
theorem let_pair_slots_proof {m : Nat} {Γ : BoundCtx (Ty α) m} {A B C : Ty α} (p q : Fin m)
    (hp : Γ.get p = A) (hq : Γ.get q = B) {body : LetCase.LocallyNameless.Tm Empty Φ (m + 2)}
    (hBody : HasType Φ Γ₀ ((Γ.snoc A).snoc B) body C) :
    Equiv false Γ₀ Γ (.let₂ (.pair (.bv p) (.bv q)) body)
      (body.rename (Fin.cases q (Fin.cases p (fun i => i)))) C := by
  subst hp
  subst hq
  have hA : HasType Φ Γ₀ Γ (.bv p) (Γ.get p) := .bv
  have hB : HasType Φ Γ₀ Γ (.bv q) (Γ.get q) := .bv
  have split := Equiv.pairBeta (pureEff := false) hA hB hBody
  have first := Equiv.letBeta (pureEff := false) Pure.bv hA (.let₁ hB.lift hBody)
  have first_eq : LetCase.LocallyNameless.Tm.instantiate
      (.let₁ (LetCase.LocallyNameless.Tm.lift (.bv q)) body) (.bv p) =
      .let₁ (.bv q) (LetCase.LocallyNameless.Tm.bsubst
        (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv p) (fun i => .bv i))) body) := rfl
  rw [first_eq] at first
  obtain ⟨-, typed⟩ := first.hasType
  cases typed with
  | let₁ hV hZ =>
    cases hV
    have second := Equiv.letBeta (pureEff := false) Pure.bv hB hZ
    have second_eq : LetCase.LocallyNameless.Tm.instantiate
        (LetCase.LocallyNameless.Tm.bsubst
          (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv p) (fun i => .bv i))) body)
        (.bv q) = body.rename (Fin.cases q (Fin.cases p (fun i => i))) := by
      simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_comp]
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ body)
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    rw [second_eq] at second
    exact split.trans (first.trans second)

/-- Two pattern lets on pair slots commute. -/
theorem let_pair_pair_comm_proof {m : Nat} {Γ : BoundCtx (Ty α) m} {A B C D E : Ty α} (i j : Fin m)
    (hi : Γ.get i = .product C D) (hj : Γ.get j = .product A B)
    {body : LetCase.LocallyNameless.Tm Empty Φ (m + 4)}
    (hBody : HasType Φ Γ₀ ((((Γ.snoc C).snoc D).snoc A).snoc B) body E) :
    Equiv false Γ₀ Γ (.let₂ (.bv i) (.let₂ (.bv j.succ.succ) body))
      (.let₂ (.bv j) (.let₂ (.bv i.succ.succ) (body.rename afterPairPair))) E := by
  have hx : HasType Φ Γ₀ Γ (.bv j) (.product A B) := hj ▸ .bv
  have hy : HasType Φ Γ₀ Γ (.bv i) (.product C D) := hi ▸ .bv
  let ins := ((((BoundCtx.Renaming.succ Γ (.product A B)).up C).up D).up A).up B
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) :=
    .let₂ (.bv i.succ) (.let₂ (.bv 2) (body.rename ins.toFun))
  have hK : HasType Φ Γ₀ (Γ.snoc (.product A B)) K E :=
    .let₂ (HasType.rename (BoundCtx.Renaming.succ Γ (.product A B)) hy)
      (.let₂ (.bv (ι := (2 : Fin (m + 3)))) (HasType.rename ins hBody))
  have enter := Equiv.letBeta (pureEff := false) Pure.bv hx hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv j) =
      .let₂ (.bv i) (.let₂ (.bv j.succ.succ) body) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    congr 1
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
      (LetCase.LocallyNameless.Tm.bsubst_id body)
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at enter
  have eta := Equiv.let₁ (Equiv.pairEta (pureEff := false) hx).symm (.refl hK)
  have pull := Equiv.bindLetPair (pureEff := false) hx
    (.pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))) hK
  have hPair : HasType Φ Γ₀ ((Γ.snoc A).snoc B) (.pair (.bv 1) (.bv 0)) (.product A B) :=
    .pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))
  have beta := Equiv.letBeta (pureEff := false) (Pure.pair Pure.bv Pure.bv) hPair hK.underBinder.underBinder
  let past : BoundCtx.Renaming Γ ((Γ.snoc A).snoc B) :=
    (BoundCtx.Renaming.succ Γ A).comp (BoundCtx.Renaming.succ (Γ.snoc A) B)
  let ins2 := (((past.up C).up D).up A).up B
  have beta_eq : LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder (.pair (.bv 1) (.bv 0)) =
      .let₂ (.bv i.succ.succ) (.let₂ (.pair (.bv 3) (.bv 2)) (body.rename ins2.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename,
      LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    congr 1
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
      (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename ins2.toFun body)
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [beta_eq] at beta
  have hBody₂ : HasType Φ Γ₀ ((((((Γ.snoc A).snoc B).snoc C).snoc D).snoc A).snoc B)
      (body.rename ins2.toFun) E := HasType.rename ins2 hBody
  have slots := let_pair_slots_proof (Γ := (((Γ.snoc A).snoc B).snoc C).snoc D) 3 2 rfl rfl hBody₂
  have moved : (body.rename ins2.toFun).rename (Fin.cases 2 (Fin.cases 3 (fun i => i))) =
      body.rename afterPairPair := by
    rw [LetCase.LocallyNameless.Tm.rename_comp]
    apply LetCase.LocallyNameless.Tm.rename_congr
    intro l
    refine Fin.cases rfl (fun l => ?_) l
    refine Fin.cases rfl (fun l => ?_) l
    refine Fin.cases rfl (fun l => ?_) l
    exact Fin.cases rfl (fun l => rfl) l
  rw [moved] at slots
  have hy'' : HasType Φ Γ₀ ((Γ.snoc A).snoc B) (.bv i.succ.succ) (.product C D) := HasType.rename past hy
  exact enter.symm.trans (eta.trans (pull.trans (Equiv.let₂ (.refl hx)
    (beta.trans (Equiv.let₂ (.refl hy'') slots)))))

end Interchange

section Unpack

variable [HasTy Φ (Ty α)]

/-- A slot is typed at its type. -/
theorem slot_typed {k : Nat} {Γ : BoundCtx (Ty α) k} (i : Fin k) {A : Ty α} (h : Γ.get i = A) :
    HasType Φ Γ₀ Γ (.bv i) A := h ▸ .bv

/-- Unpacking is typed when the unpacked slot has the tuple type. -/
theorem unpackAt_typed_proof : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (i : Fin k) →
    Γ.get i = tupleTy atoms → {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))} →
    {C : Ty α} → HasType Φ Γ₀ (extendCtx Γ (pairsTele atoms)) u C → HasType Φ Γ₀ Γ (unpackAt atoms i u) C
  | [], _, _, _, _, _, _, h => h
  | [_], _, _, _, _, _, _, h => h
  | _ :: d :: more, _, _, i, hi, _, _, h =>
    .let₂ (slot_typed i hi) (unpackAt_typed_proof (d :: more) 0 rfl h)

/-- Unpacking preserves native equations. -/
theorem unpackAt_congr_proof : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (i : Fin k) →
    Γ.get i = tupleTy atoms → {u v : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))} →
    {C : Ty α} → Equiv false Γ₀ (extendCtx Γ (pairsTele atoms)) u v C →
    Equiv false Γ₀ Γ (unpackAt atoms i u) (unpackAt atoms i v) C
  | [], _, _, _, _, _, _, _, h => h
  | [_], _, _, _, _, _, _, _, h => h
  | _ :: d :: more, _, _, i, hi, _, _, _, h =>
    Equiv.let₂ (.refl (slot_typed i hi)) (unpackAt_congr_proof (d :: more) 0 rfl h)

/-- A pattern let on an older pair slot, under the unpacking of a tuple
slot, is natively equal to the pattern let in front of the unpacking. One
interchange of pattern lets is used for each pattern let of the
unpacking. -/
theorem unpack_pair_comm_proof : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (i j : Fin k) →
    Γ.get i = tupleTy atoms → {A B C : Ty α} → Γ.get j = .product A B →
    {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms) + 1 + 1)} →
    HasType Φ Γ₀ (((extendCtx Γ (pairsTele atoms)).snoc A).snoc B) body C →
    Equiv false Γ₀ Γ
      (unpackAt atoms i (.let₂ (.bv ((weakenTele Γ (pairsTele atoms)).toFun j)) body))
      (.let₂ (.bv j) (unpackAt atoms i.succ.succ
        (body.rename (pairPastTele Γ (pairsTele atoms) A B).toFun))) C
  | [], _, Γ, _, j, _, A, B, _, hj, body, hBody => by
    have same : body.rename (pairPastTele Γ (pairsTele ([] : List α)) A B).toFun = body :=
      (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) body).trans
        (LetCase.LocallyNameless.Tm.rename_id body)
    exact Equiv.let₂ (.refl (slot_typed j hj))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (((extendCtx Γ (pairsTele ([] : List α))).snoc A).snoc B) body x _)
        same.symm (.refl hBody))
  | [c], _, Γ, _, j, _, A, B, _, hj, body, hBody => by
    have same : body.rename (pairPastTele Γ (pairsTele [c]) A B).toFun = body :=
      (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) body).trans
        (LetCase.LocallyNameless.Tm.rename_id body)
    exact Equiv.let₂ (.refl (slot_typed j hj))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (((extendCtx Γ (pairsTele [c])).snoc A).snoc B) body x _)
        same.symm (.refl hBody))
  | c :: d :: more, _, Γ, i, j, hi, A, B, C, hj, body, hBody => by
    let R : Ty α := tupleTy (d :: more)
    let Γ₂ := (Γ.snoc (.base c)).snoc R
    have ih := unpack_pair_comm_proof (d :: more) (Γ := Γ₂) 0 j.succ.succ rfl hj hBody
    have hZ : HasType Φ Γ₀ ((Γ₂.snoc A).snoc B)
        (unpackAt (d :: more) (2 : Fin (_ + 4))
          (body.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B).toFun)) C :=
      unpackAt_typed_proof (d :: more) (Γ := (Γ₂.snoc A).snoc B) 2 rfl
        (HasType.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B) hBody)
    have comm := let_pair_pair_comm_proof i j hi hj hZ
    have moved : (unpackAt (d :: more) (2 : Fin (_ + 4))
        (body.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B).toFun)).rename afterPairPair =
        unpackAt (d :: more) (0 : Fin (_ + 4))
          (body.rename (pairPastTele Γ (pairsTele (c :: d :: more)) A B).toFun) := by
      have step := unpackAt_rename (Φ := Φ) (d :: more) (afterPairPairRenaming Γ (.base c) R A B) 2
        (body.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B).toFun)
      have total : pairPastTele Γ (pairsTele (c :: d :: more)) A B =
          (pairPastTele Γ₂ (pairsTele (d :: more)) A B).comp
            (upTele (afterPairPairRenaming Γ (.base c) R A B) (pairsTele (d :: more))) := by
        have outer := pairPastTele_cons (R :: pairsTele (d :: more)) Γ (.base c) A B
        rw [pairPastTele_cons (pairsTele (d :: more)) (Γ.snoc (.base c)) R A B] at outer
        rw [afterPairPair_split, ← upTele_comp]
        exact outer
      rw [total]
      exact step.trans (congrArg (unpackAt (d :: more) 0) (LetCase.LocallyNameless.Tm.rename_comp _ _ body))
    rw [moved] at comm
    exact (Equiv.let₂ (.refl (slot_typed i hi)) ih).trans comm

/-- A bound tuple that is unpacked, followed by a pattern let on an older
pair slot, is natively equal to the pattern let in front of the binding:

`let₁ E (unpack (let₂ x B)) = let₂ x (let₁ E↑↑ (unpack B′))`

where `unpack` is the sequence of pattern lets that unpacks the bound
tuple, `E↑↑` is `E` weakened past the two components, and `B′` is `B` with
the two components moved beneath the tuple slot and the slots of its
unpacking. `E` may be an effectful request. -/
theorem let_unpack_pair_comm_proof (atoms : List α) {k : Nat} {Δ : BoundCtx (Ty α) k} (j : Fin k)
    {A B C : Ty α} (hj : Δ.get j = .product A B) {E : LetCase.LocallyNameless.Tm Empty Φ k}
    (hE : HasType Φ Γ₀ Δ E (tupleTy atoms))
    {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms) + 1 + 1)}
    (hBody : HasType Φ Γ₀ (((extendCtx Δ (unpackTele atoms)).snoc A).snoc B) body C) :
    Equiv false Γ₀ Δ
      (.let₁ E (unpackAt atoms 0 (.let₂ (.bv ((weakenTele Δ (unpackTele atoms)).toFun j)) body)))
      (.let₂ (.bv j) (.let₁ (E.rename (pastPair Δ A B).toFun)
        (unpackAt atoms 0 (body.rename (pairPastTele Δ (unpackTele atoms) A B).toFun)))) C := by
  let X : Ty α := tupleTy atoms
  have inner := unpack_pair_comm_proof atoms (Γ := Δ.snoc X) 0 j.succ rfl hj hBody
  have hZ : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B)
      (unpackAt atoms (2 : Fin (k + 3)) (body.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B).toFun)) C :=
    unpackAt_typed_proof atoms (Γ := ((Δ.snoc X).snoc A).snoc B) 2 rfl
      (HasType.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B) hBody)
  have comm := let_pair_comm_proof j hj hE hZ
  have moved : (unpackAt atoms (2 : Fin (k + 3))
      (body.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B).toFun)).rename afterPair =
      unpackAt atoms (0 : Fin (k + 3)) (body.rename (pairPastTele Δ (unpackTele atoms) A B).toFun) := by
    have step := unpackAt_rename (Φ := Φ) atoms (afterPairRenaming Δ X A B) 2
      (body.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B).toFun)
    rw [pairPastTele_cons (pairsTele atoms) Δ X A B]
    exact step.trans (congrArg (unpackAt atoms 0) (LetCase.LocallyNameless.Tm.rename_comp _ _ body))
  rw [moved] at comm
  exact (Equiv.let₁ (.refl hE) inner).trans comm

end Unpack

/-! ## A case commutes with a pattern let on a pair slot

A case on a slot whose two arms destructure the same older pair slot is
natively equal to destructuring first. The case is not moved across any
request and keeps its scrutinee. -/

section CasePair

variable [HasTy Φ (Ty α)]

/-- A term over a pair slot is natively equal to destructuring the slot
and using the pair of components in its place:

`K[x] = let₂ x (K[(a, b)])`

for a slot `x` of pair type. `K` may be any typed term, with requests and
cases. This is the common step of the equations that move a pattern let
on a pair slot: pure-let beta at the slot, pair eta, the sequencing law
that pulls a pattern let out of the scrutinee of a let, and pure-let beta
at the pair of components. -/
theorem slot_pair_split_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {A B C : Ty α} (j : Fin m)
    (hj : Δ.get j = .product A B) {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
    (hK : HasType Φ Γ₀ (Δ.snoc (.product A B)) K C) :
    Equiv false Γ₀ Δ (LetCase.LocallyNameless.Tm.instantiate K (.bv j))
      (.let₂ (.bv j) (LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder
        (.pair (.bv 1) (.bv 0)))) C := by
  have hx : HasType Φ Γ₀ Δ (.bv j) (.product A B) := hj ▸ .bv
  have enter := Equiv.letBeta (pureEff := false) Pure.bv hx hK
  have eta := Equiv.let₁ (Equiv.pairEta (pureEff := false) hx).symm (.refl hK)
  have pull := Equiv.bindLetPair (pureEff := false) hx
    (.pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))) hK
  have hPair : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (.pair (.bv 1) (.bv 0)) (.product A B) :=
    .pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))
  have beta := Equiv.letBeta (pureEff := false) (Pure.pair Pure.bv Pure.bv) hPair hK.underBinder.underBinder
  exact enter.symm.trans (eta.trans (pull.trans (Equiv.let₂ (.refl hx) beta)))

/-- A case on a slot whose two arms destructure the same older pair slot
is natively equal to destructuring the pair slot first:

`case s (let₂ x L) (let₂ x R) = let₂ x (case s L′ R′)`

where `s` is a slot of sum type, `x` a slot of pair type, and `L′`, `R′`
are the arms with the two components moved beneath the arm's payload. The
case stays on the same scrutinee and keeps its place; only the pure
destructuring moves. -/
theorem case_pair_comm_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {A B X Y C : Ty α} (i j : Fin m)
    (hi : Δ.get i = .coprod X Y) (hj : Δ.get j = .product A B)
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 3)}
    (hl : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B) l C)
    (hr : HasType Φ Γ₀ (((Δ.snoc Y).snoc A).snoc B) r C) :
    Equiv false Γ₀ Δ (.case (.bv i) (.let₂ (.bv j.succ) l) (.let₂ (.bv j.succ) r))
      (.let₂ (.bv j) (.case (.bv i.succ.succ) (l.rename afterPair) (r.rename afterPair))) C := by
  have hs : HasType Φ Γ₀ Δ (.bv i) (.coprod X Y) := hi ▸ .bv
  let insX := (((BoundCtx.Renaming.succ Δ (.product A B)).up X).up A).up B
  let insY := (((BoundCtx.Renaming.succ Δ (.product A B)).up Y).up A).up B
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) :=
    .case (.bv i.succ) (.let₂ (.bv 1) (l.rename insX.toFun)) (.let₂ (.bv 1) (r.rename insY.toFun))
  have hK : HasType Φ Γ₀ (Δ.snoc (.product A B)) K C :=
    .case (HasType.rename (BoundCtx.Renaming.succ Δ (.product A B)) hs)
      (.let₂ (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename insX hl))
      (.let₂ (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename insY hr))
  have split := slot_pair_split_proof j hj hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv j) =
      .case (.bv i) (.let₂ (.bv j.succ) l) (.let₂ (.bv j.succ) r) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
        (LetCase.LocallyNameless.Tm.bsubst_id l)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
        (LetCase.LocallyNameless.Tm.bsubst_id r)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at split
  let past : BoundCtx.Renaming Δ ((Δ.snoc A).snoc B) :=
    (BoundCtx.Renaming.succ Δ A).comp (BoundCtx.Renaming.succ (Δ.snoc A) B)
  let insX2 := ((past.up X).up A).up B
  let insY2 := ((past.up Y).up A).up B
  have beta_eq : LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder (.pair (.bv 1) (.bv 0)) =
      .case (.bv i.succ.succ) (.let₂ (.pair (.bv 2) (.bv 1)) (l.rename insX2.toFun))
        (.let₂ (.pair (.bv 2) (.bv 1)) (r.rename insY2.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename,
      LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insX2.toFun l)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insY2.toFun r)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [beta_eq] at split
  have slotsX := let_pair_slots_proof (Γ := ((Δ.snoc A).snoc B).snoc X) 2 1 rfl rfl (HasType.rename insX2 hl)
  have slotsY := let_pair_slots_proof (Γ := ((Δ.snoc A).snoc B).snoc Y) 2 1 rfl rfl (HasType.rename insY2 hr)
  have movedX : (l.rename insX2.toFun).rename (Fin.cases 1 (Fin.cases 2 (fun i => i))) =
      l.rename afterPair := by
    rw [LetCase.LocallyNameless.Tm.rename_comp]
    apply LetCase.LocallyNameless.Tm.rename_congr
    intro i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  have movedY : (r.rename insY2.toFun).rename (Fin.cases 1 (Fin.cases 2 (fun i => i))) =
      r.rename afterPair := by
    rw [LetCase.LocallyNameless.Tm.rename_comp]
    apply LetCase.LocallyNameless.Tm.rename_congr
    intro i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [movedX] at slotsX
  rw [movedY] at slotsY
  have hs'' : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (.bv i.succ.succ) (.coprod X Y) := HasType.rename past hs
  have hx : HasType Φ Γ₀ Δ (.bv j) (.product A B) := hj ▸ .bv
  exact split.trans (Equiv.let₂ (.refl hx) (Equiv.case (.refl hs'') slotsX slotsY))

end CasePair

/-! ## Moving a whole unpacking

The unpacking of an older tuple slot moves in front of a binding, and in
front of a case whose arms both unpack it, by induction on the tuple. -/

section Out

variable [HasTy Φ (Ty α)]

/-- The whole unpacking of an older tuple slot moves in front of an action
on terms that moves single pattern lets. -/
theorem unpack_out_proof {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (frame : PairFrame C Ω tel term) :
    (H : List α) → {k : Nat} → {Ω' : BoundCtx (Ty α) k} → (ω : BoundCtx.Renaming Ω Ω') → (j : Fin k) →
    Ω'.get j = tupleTy H →
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize (teleSize k tel) (pairsTele H))} →
    HasType Φ Γ₀ (extendCtx (extendCtx Ω' tel) (pairsTele H)) u C →
    Equiv false Γ₀ Ω' (term ω (unpackAt H ((weakenTele Ω' tel).toFun j) u))
      (unpackAt H j (term (ω.comp (weakenTele Ω' (pairsTele H)))
        (u.rename (swapTeles Ω' tel (pairsTele H)).toFun))) C
  | [], _, Ω', ω, _, _, u, hu =>
    Eq.subst (motive := fun x => Equiv false Γ₀ Ω' (term ω u)
      (term (ω.comp (weakenTele Ω' (pairsTele ([] : List α)))) x) C)
      (LetCase.LocallyNameless.Tm.rename_id u).symm (.refl (frame.typed ω hu))
  | [c], _, Ω', ω, _, _, u, hu =>
    Eq.subst (motive := fun x => Equiv false Γ₀ Ω' (term ω u)
      (term (ω.comp (weakenTele Ω' (pairsTele [c]))) x) C)
      (LetCase.LocallyNameless.Tm.rename_id u).symm (.refl (frame.typed ω hu))
  | c :: d :: more, k, Ω', ω, j, hj, u, hu => by
    let R : Ty α := tupleTy (d :: more)
    let pp := pairPastTele Ω' tel (.base c) R
    have hB : HasType Φ Γ₀ (((extendCtx Ω' tel).snoc (.base c)).snoc R) (unpackAt (d :: more) 0 u) C :=
      unpackAt_typed_proof (d :: more) (Γ := ((extendCtx Ω' tel).snoc (.base c)).snoc R) 0 rfl hu
    have comm := frame.comm ω j hj hB
    have e1 : (unpackAt (d :: more) (0 : Fin (teleSize k tel + 1 + 1)) u).rename pp.toFun =
        unpackAt (d :: more) ((weakenTele ((Ω'.snoc (.base c)).snoc R) tel).toFun 0)
          (u.rename (upTele pp (pairsTele (d :: more))).toFun) :=
      (unpackAt_rename (Φ := Φ) (d :: more) pp 0 u).trans
        (congrArg (fun i => unpackAt (d :: more) i (u.rename (upTele pp (pairsTele (d :: more))).toFun))
          (pairPastTele_zero tel Ω' (.base c) R))
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ Ω'
      (term ω (.let₂ (.bv ((weakenTele Ω' tel).toFun j)) (unpackAt (d :: more) 0 u)))
      (.let₂ (.bv j) (term (ω.comp (pastPair Ω' (.base c) R)) x)) C) e1 comm
    have ih := unpack_out_proof frame (d :: more) (ω.comp (pastPair Ω' (.base c) R)) (0 : Fin (k + 2)) rfl
      (HasType.rename (upTele pp (pairsTele (d :: more))) hu)
    have e2 : (u.rename (upTele pp (pairsTele (d :: more))).toFun).rename
        (swapTeles ((Ω'.snoc (.base c)).snoc R) tel (pairsTele (d :: more))).toFun =
        u.rename (swapTeles Ω' tel (pairsTele (c :: d :: more))).toFun :=
      (LetCase.LocallyNameless.Tm.rename_comp _ _ u).trans
        (congrArg (fun r : BoundCtx.Renaming _ _ => u.rename r.toFun)
          (swapTeles_pair (pairsTele (d :: more)) Ω' tel (.base c) R).symm)
    have ih' := Eq.subst (motive := fun x => Equiv false Γ₀ ((Ω'.snoc (.base c)).snoc R)
      (term (ω.comp (pastPair Ω' (.base c) R)) (unpackAt (d :: more)
        ((weakenTele ((Ω'.snoc (.base c)).snoc R) tel).toFun 0)
        (u.rename (upTele pp (pairsTele (d :: more))).toFun)))
      (unpackAt (d :: more) 0 (term ((ω.comp (pastPair Ω' (.base c) R)).comp
        (weakenTele ((Ω'.snoc (.base c)).snoc R) (pairsTele (d :: more)))) x)) C) e2 ih
    exact comm'.trans (Equiv.let₂ (.refl (slot_typed j hj)) ih')

/-- The whole unpacking of an older tuple slot, done in both arms of a
case on a slot, moves in front of the case. The case stays on the same
scrutinee. One exchange of the case with a pattern let is used for each
pattern let of the unpacking. -/
theorem case_unpack_out_proof {C : Ty α} : (H : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} →
    (i j : Fin k) → {X Y : Ty α} → Γ.get i = .coprod X Y → Γ.get j = tupleTy H →
    {l r : LetCase.LocallyNameless.Tm Empty Φ (teleSize (k + 1) (pairsTele H))} →
    HasType Φ Γ₀ (extendCtx (Γ.snoc X) (pairsTele H)) l C →
    HasType Φ Γ₀ (extendCtx (Γ.snoc Y) (pairsTele H)) r C →
    Equiv false Γ₀ Γ (.case (.bv i) (unpackAt H j.succ l) (unpackAt H j.succ r))
      (unpackAt H j (.case (.bv ((weakenTele Γ (pairsTele H)).toFun i))
        (l.rename (swapTeles Γ [X] (pairsTele H)).toFun)
        (r.rename (swapTeles Γ [Y] (pairsTele H)).toFun))) C
  | [], _, Γ, i, _, X, Y, hi, _, l, r, hl, hr =>
    Equiv.case (.refl (slot_typed i hi))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc X) l x C)
        (LetCase.LocallyNameless.Tm.rename_id l).symm (.refl hl))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc Y) r x C)
        (LetCase.LocallyNameless.Tm.rename_id r).symm (.refl hr))
  | [_], _, Γ, i, _, X, Y, hi, _, l, r, hl, hr =>
    Equiv.case (.refl (slot_typed i hi))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc X) l x C)
        (LetCase.LocallyNameless.Tm.rename_id l).symm (.refl hl))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc Y) r x C)
        (LetCase.LocallyNameless.Tm.rename_id r).symm (.refl hr))
  | c :: d :: more, k, Γ, i, j, X, Y, hi, hj, l, r, hl, hr => by
    let R : Ty α := tupleTy (d :: more)
    let Γ₂ := (Γ.snoc (.base c)).snoc R
    have hl₁ : HasType Φ Γ₀ (((Γ.snoc X).snoc (.base c)).snoc R) (unpackAt (d :: more) 0 l) C :=
      unpackAt_typed_proof (d :: more) (Γ := ((Γ.snoc X).snoc (.base c)).snoc R) 0 rfl hl
    have hr₁ : HasType Φ Γ₀ (((Γ.snoc Y).snoc (.base c)).snoc R) (unpackAt (d :: more) 0 r) C :=
      unpackAt_typed_proof (d :: more) (Γ := ((Γ.snoc Y).snoc (.base c)).snoc R) 0 rfl hr
    have comm := case_pair_comm_proof i j hi hj hl₁ hr₁
    have movedL := unpackAt_rename (Φ := Φ) (d :: more) (afterPairRenaming Γ X (.base c) R) 0 l
    have movedR := unpackAt_rename (Φ := Φ) (d :: more) (afterPairRenaming Γ Y (.base c) R) 0 r
    have ih := case_unpack_out_proof (C := C) (d :: more) (Γ := Γ₂) i.succ.succ 0 hi rfl
      (HasType.rename (upTele (afterPairRenaming Γ X (.base c) R) (pairsTele (d :: more))) hl)
      (HasType.rename (upTele (afterPairRenaming Γ Y (.base c) R) (pairsTele (d :: more))) hr)
    have total (Z : Ty α) (t : LetCase.LocallyNameless.Tm Empty Φ (teleSize (k + 1) (pairsTele (c :: d :: more)))) :
        (t.rename (upTele (afterPairRenaming Γ Z (.base c) R) (pairsTele (d :: more))).toFun).rename
          (swapTeles Γ₂ [Z] (pairsTele (d :: more))).toFun =
        t.rename (swapTeles Γ [Z] (pairsTele (c :: d :: more))).toFun := by
      have e := swapTeles_pair (pairsTele (d :: more)) Γ [Z] (.base c) R
      rw [pairPastTele_single] at e
      exact (LetCase.LocallyNameless.Tm.rename_comp _ _ t).trans
        (congrArg (fun r : BoundCtx.Renaming _ _ => t.rename r.toFun) e.symm)
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ Γ
      (.case (.bv i) (.let₂ (.bv j.succ) (unpackAt (d :: more) 0 l)) (.let₂ (.bv j.succ) (unpackAt (d :: more) 0 r)))
      (.let₂ (.bv j) x) C)
      (congrArg₂ (fun x y => LetCase.LocallyNameless.Tm.case (.bv i.succ.succ) x y) movedL movedR) comm
    have ih' := Eq.subst (motive := fun x => Equiv false Γ₀ Γ₂
      (.case (.bv i.succ.succ)
        (unpackAt (d :: more) (1 : Fin (k + 3))
          (l.rename (upTele (afterPairRenaming Γ X (.base c) R) (pairsTele (d :: more))).toFun))
        (unpackAt (d :: more) (1 : Fin (k + 3))
          (r.rename (upTele (afterPairRenaming Γ Y (.base c) R) (pairsTele (d :: more))).toFun)))
      (unpackAt (d :: more) 0 x) C)
      (congrArg₂ (fun x y => LetCase.LocallyNameless.Tm.case
        (.bv ((weakenTele Γ₂ (pairsTele (d :: more))).toFun i.succ.succ)) x y) (total X l) (total Y r)) ih
    exact comm'.trans (Equiv.let₂ (.refl (slot_typed j hj)) ih')

end Out

/-! ## A stored sum slot is inspected before a later binding

A case on a slot of sum type may be moved in front of a binding that
precedes it. The slot is a variable, so the tag test is pure. The binding
is copied into both arms. On every run exactly one arm is taken, so the
binding is evaluated once, and after the same earlier bindings. -/

section CaseSlot

variable [HasTy Φ (Ty α)]

/-- A term over a slot of sum type is natively equal to the case on the
slot around the term at each injection of the payload:

`K[s] = case s (K[inl a]) (K[inr b])`

for a slot `s` of sum type. `K` may be any typed term, with requests. It
is derived from native typed laws: pure-let beta at the slot, sum eta, the
sequencing law that pulls a case out of the scrutinee of a let, and
pure-let beta at an injection of a slot. -/
theorem slot_sum_split_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {X Y C : Ty α} (j : Fin m)
    (hj : Δ.get j = .coprod X Y) {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
    (hK : HasType Φ Γ₀ (Δ.snoc (.coprod X Y)) K C) :
    Equiv false Γ₀ Δ (LetCase.LocallyNameless.Tm.instantiate K (.bv j))
      (.case (.bv j)
        (LetCase.LocallyNameless.Tm.instantiate K.underBinder (.inl (.bv 0)))
        (LetCase.LocallyNameless.Tm.instantiate K.underBinder (.inr (.bv 0)))) C := by
  have hx : HasType Φ Γ₀ Δ (.bv j) (.coprod X Y) := hj ▸ .bv
  have hl : HasType Φ Γ₀ (Δ.snoc X) (.inl (.bv 0)) (.coprod X Y) := .inl (.bv (ι := (0 : Fin (m + 1))))
  have hr : HasType Φ Γ₀ (Δ.snoc Y) (.inr (.bv 0)) (.coprod X Y) := .inr (.bv (ι := (0 : Fin (m + 1))))
  have enter := Equiv.letBeta (pureEff := false) Pure.bv hx hK
  have eta := Equiv.let₁ (Equiv.caseEta (pureEff := false) hx).symm (.refl hK)
  have pull := Equiv.bindLetCase (pureEff := false) hx hl hr hK
  have betaL := Equiv.letBeta (pureEff := false) (Pure.inl Pure.bv) hl hK.underBinder
  have betaR := Equiv.letBeta (pureEff := false) (Pure.inr Pure.bv) hr hK.underBinder
  exact enter.symm.trans (eta.trans (pull.trans (Equiv.case (.refl hx) betaL betaR)))

/-- A binding followed by a case on an older slot of sum type is natively
equal to the case followed by the binding in each arm:

`let₁ E (case s L R) = case s (let₁ E↑ L′) (let₁ E↑ R′)`

where `s` is a slot of sum type, `E↑` is `E` weakened past the payload of
the arm, and `L′`, `R′` are the arms with the payload moved beneath the
binder of the let. `E` may be an effectful request. It is typed where `s`
is a slot of sum type, so it cannot depend on which tag `s` carries. This
is not an axiom of the native theory. It follows from the equation above
and case beta at an injection. -/
theorem let_case_comm_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {X Y Z C : Ty α} (i : Fin m)
    (hi : Δ.get i = .coprod X Y) {E : LetCase.LocallyNameless.Tm Empty Φ m}
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 2)} (hE : HasType Φ Γ₀ Δ E Z)
    (hl : HasType Φ Γ₀ ((Δ.snoc Z).snoc X) l C) (hr : HasType Φ Γ₀ ((Δ.snoc Z).snoc Y) r C) :
    Equiv false Γ₀ Δ (.let₁ E (.case (.bv i.succ) l r))
      (.case (.bv i)
        (.let₁ (E.rename Fin.succ) (l.rename (swapRenaming Δ Z X).toFun))
        (.let₁ (E.rename Fin.succ) (r.rename (swapRenaming Δ Z Y).toFun))) C := by
  let S : Ty α := .coprod X Y
  let insX := ((BoundCtx.Renaming.succ Δ S).up Z).up X
  let insY := ((BoundCtx.Renaming.succ Δ S).up Z).up Y
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) :=
    .let₁ (E.rename Fin.succ) (.case (.bv 1) (l.rename insX.toFun) (r.rename insY.toFun))
  have hK : HasType Φ Γ₀ (Δ.snoc S) K C :=
    .let₁ (HasType.rename (BoundCtx.Renaming.succ Δ S) hE)
      (.case (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename insX hl) (HasType.rename insY hr))
  have split := slot_sum_split_proof i hi hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv i) = .let₁ E (.case (.bv i.succ) l r) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · exact (LetCase.LocallyNameless.Tm.bsubst_congr (fun _ => rfl) E).trans
        (LetCase.LocallyNameless.Tm.bsubst_id E)
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
          (LetCase.LocallyNameless.Tm.bsubst_id l)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
          (LetCase.LocallyNameless.Tm.bsubst_id r)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at split
  let insX2 := ((BoundCtx.Renaming.succ Δ X).up Z).up X
  let insY2 := ((BoundCtx.Renaming.succ Δ Y).up Z).up Y
  let insYX := ((BoundCtx.Renaming.succ Δ X).up Z).up Y
  let insXY := ((BoundCtx.Renaming.succ Δ Y).up Z).up X
  have eqL : LetCase.LocallyNameless.Tm.instantiate K.underBinder (.inl (.bv 0)) =
      .let₁ (E.rename Fin.succ) (.case (.inl (.bv 1)) (l.rename insX2.toFun) (r.rename insYX.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename,
      LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · exact (LetCase.LocallyNameless.Tm.bsubst_congr (fun _ => rfl) E).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ E)
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
          (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insX2.toFun l)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
          (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insYX.toFun r)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
  have eqR : LetCase.LocallyNameless.Tm.instantiate K.underBinder (.inr (.bv 0)) =
      .let₁ (E.rename Fin.succ) (.case (.inr (.bv 1)) (l.rename insXY.toFun) (r.rename insY2.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename,
      LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · exact (LetCase.LocallyNameless.Tm.bsubst_congr (fun _ => rfl) E).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ E)
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
          (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insXY.toFun l)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
          (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insY2.toFun r)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
  rw [eqL, eqR] at split
  -- case beta at the injection, then pure-let beta at the payload slot
  have hEX : HasType Φ Γ₀ (Δ.snoc X) (E.rename Fin.succ) Z := HasType.rename (BoundCtx.Renaming.succ Δ X) hE
  have hEY : HasType Φ Γ₀ (Δ.snoc Y) (E.rename Fin.succ) Z := HasType.rename (BoundCtx.Renaming.succ Δ Y) hE
  have hlX : HasType Φ Γ₀ (((Δ.snoc X).snoc Z).snoc X) (l.rename insX2.toFun) C := HasType.rename insX2 hl
  have hrX : HasType Φ Γ₀ (((Δ.snoc X).snoc Z).snoc Y) (r.rename insYX.toFun) C := HasType.rename insYX hr
  have hlY : HasType Φ Γ₀ (((Δ.snoc Y).snoc Z).snoc X) (l.rename insXY.toFun) C := HasType.rename insXY hl
  have hrY : HasType Φ Γ₀ (((Δ.snoc Y).snoc Z).snoc Y) (r.rename insY2.toFun) C := HasType.rename insY2 hr
  have hpX : HasType Φ Γ₀ ((Δ.snoc X).snoc Z) (.bv 1) X := .bv (ι := (1 : Fin (m + 2)))
  have hpY : HasType Φ Γ₀ ((Δ.snoc Y).snoc Z) (.bv 1) Y := .bv (ι := (1 : Fin (m + 2)))
  have caseL := Equiv.caseBetaL (pureEff := false) hpX hlX hrX
  have caseR := Equiv.caseBetaR (pureEff := false) hpY hlY hrY
  have substL := Equiv.letBeta (pureEff := false) Pure.bv hpX hlX
  have substR := Equiv.letBeta (pureEff := false) Pure.bv hpY hrY
  have movedL : LetCase.LocallyNameless.Tm.instantiate (l.rename insX2.toFun) (.bv (1 : Fin (m + 2))) =
      l.rename (swapRenaming Δ Z X).toFun := by
    simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_rename]
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
      (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename (swapRenaming Δ Z X).toFun l)
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  have movedR : LetCase.LocallyNameless.Tm.instantiate (r.rename insY2.toFun) (.bv (1 : Fin (m + 2))) =
      r.rename (swapRenaming Δ Z Y).toFun := by
    simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_rename]
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
      (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename (swapRenaming Δ Z Y).toFun r)
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [movedL] at substL
  rw [movedR] at substR
  have hs : HasType Φ Γ₀ Δ (.bv i) (.coprod X Y) := hi ▸ .bv
  exact split.trans (Equiv.case (.refl hs)
    (Equiv.let₁ (.refl hEX) (caseL.trans substL)) (Equiv.let₁ (.refl hEY) (caseR.trans substR)))

/-- The arm of a case on the first injection of a slot, under one more
slot `Z`, is the first arm with the payload beneath `Z`. Case beta at the
injection and pure-let beta at the payload slot. -/
theorem sum_arm_inl_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {X Y Z C : Ty α}
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 2)} (hl : HasType Φ Γ₀ ((Δ.snoc Z).snoc X) l C)
    (hr : HasType Φ Γ₀ ((Δ.snoc Z).snoc Y) r C) :
    Equiv false Γ₀ ((Δ.snoc X).snoc Z)
      (.case (.inl (.bv 1)) (l.rename (((BoundCtx.Renaming.succ Δ X).up Z).up X).toFun)
        (r.rename (((BoundCtx.Renaming.succ Δ X).up Z).up Y).toFun))
      (l.rename (swapRenaming Δ Z X).toFun) C := by
  let insX2 := ((BoundCtx.Renaming.succ Δ X).up Z).up X
  let insYX := ((BoundCtx.Renaming.succ Δ X).up Z).up Y
  have hlX : HasType Φ Γ₀ (((Δ.snoc X).snoc Z).snoc X) (l.rename insX2.toFun) C := HasType.rename insX2 hl
  have hrX : HasType Φ Γ₀ (((Δ.snoc X).snoc Z).snoc Y) (r.rename insYX.toFun) C := HasType.rename insYX hr
  have hpX : HasType Φ Γ₀ ((Δ.snoc X).snoc Z) (.bv 1) X := .bv (ι := (1 : Fin (m + 2)))
  have caseL := Equiv.caseBetaL (pureEff := false) hpX hlX hrX
  have substL := Equiv.letBeta (pureEff := false) Pure.bv hpX hlX
  have movedL : LetCase.LocallyNameless.Tm.instantiate (l.rename insX2.toFun) (.bv (1 : Fin (m + 2))) =
      l.rename (swapRenaming Δ Z X).toFun := by
    simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_rename]
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
      (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename (swapRenaming Δ Z X).toFun l)
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [movedL] at substL
  exact caseL.trans substL

/-- The arm of a case on the second injection of a slot, under one more
slot `Z`, is the second arm with the payload beneath `Z`. -/
theorem sum_arm_inr_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {X Y Z C : Ty α}
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 2)} (hl : HasType Φ Γ₀ ((Δ.snoc Z).snoc X) l C)
    (hr : HasType Φ Γ₀ ((Δ.snoc Z).snoc Y) r C) :
    Equiv false Γ₀ ((Δ.snoc Y).snoc Z)
      (.case (.inr (.bv 1)) (l.rename (((BoundCtx.Renaming.succ Δ Y).up Z).up X).toFun)
        (r.rename (((BoundCtx.Renaming.succ Δ Y).up Z).up Y).toFun))
      (r.rename (swapRenaming Δ Z Y).toFun) C := by
  let insXY := ((BoundCtx.Renaming.succ Δ Y).up Z).up X
  let insY2 := ((BoundCtx.Renaming.succ Δ Y).up Z).up Y
  have hlY : HasType Φ Γ₀ (((Δ.snoc Y).snoc Z).snoc X) (l.rename insXY.toFun) C := HasType.rename insXY hl
  have hrY : HasType Φ Γ₀ (((Δ.snoc Y).snoc Z).snoc Y) (r.rename insY2.toFun) C := HasType.rename insY2 hr
  have hpY : HasType Φ Γ₀ ((Δ.snoc Y).snoc Z) (.bv 1) Y := .bv (ι := (1 : Fin (m + 2)))
  have caseR := Equiv.caseBetaR (pureEff := false) hpY hlY hrY
  have substR := Equiv.letBeta (pureEff := false) Pure.bv hpY hrY
  have movedR : LetCase.LocallyNameless.Tm.instantiate (r.rename insY2.toFun) (.bv (1 : Fin (m + 2))) =
      r.rename (swapRenaming Δ Z Y).toFun := by
    simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_rename]
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
      (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename (swapRenaming Δ Z Y).toFun r)
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [movedR] at substR
  exact caseR.trans substR

/-- A case on a slot of sum type whose two arms case on an older stored
slot of sum type is natively equal to the case on the stored slot around
the case on the first slot:

`case y (case s L₁ R₁) (case s L₂ R₂) = case s (case y L₁′ L₂′) (case y R₁′ R₂′)`

where the arms have the payload of `s` moved beneath the payload of `y`.
Both scrutinees are slots, so both tag tests are pure, and no request is
moved. It is not an axiom of the native theory. It follows from the
equation that splits a term on a slot of sum type, case beta at an
injection and pure-let beta. -/
theorem case_case_comm_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {X Y A B C : Ty α} (i y : Fin m)
    (hi : Δ.get i = .coprod X Y) (hy : Δ.get y = .coprod A B)
    {l₁ r₁ l₂ r₂ : LetCase.LocallyNameless.Tm Empty Φ (m + 2)}
    (hl₁ : HasType Φ Γ₀ ((Δ.snoc A).snoc X) l₁ C) (hr₁ : HasType Φ Γ₀ ((Δ.snoc A).snoc Y) r₁ C)
    (hl₂ : HasType Φ Γ₀ ((Δ.snoc B).snoc X) l₂ C) (hr₂ : HasType Φ Γ₀ ((Δ.snoc B).snoc Y) r₂ C) :
    Equiv false Γ₀ Δ (.case (.bv y) (.case (.bv i.succ) l₁ r₁) (.case (.bv i.succ) l₂ r₂))
      (.case (.bv i)
        (.case (.bv y.succ) (l₁.rename (swapRenaming Δ A X).toFun) (l₂.rename (swapRenaming Δ B X).toFun))
        (.case (.bv y.succ) (r₁.rename (swapRenaming Δ A Y).toFun) (r₂.rename (swapRenaming Δ B Y).toFun)))
      C := by
  let S : Ty α := .coprod X Y
  let insAX := ((BoundCtx.Renaming.succ Δ S).up A).up X
  let insAY := ((BoundCtx.Renaming.succ Δ S).up A).up Y
  let insBX := ((BoundCtx.Renaming.succ Δ S).up B).up X
  let insBY := ((BoundCtx.Renaming.succ Δ S).up B).up Y
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) := .case (.bv y.succ)
    (.case (.bv 1) (l₁.rename insAX.toFun) (r₁.rename insAY.toFun))
    (.case (.bv 1) (l₂.rename insBX.toFun) (r₂.rename insBY.toFun))
  have hK : HasType Φ Γ₀ (Δ.snoc S) K C :=
    .case (slot_typed (Γ := Δ.snoc S) y.succ hy)
      (.case (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename insAX hl₁) (HasType.rename insAY hr₁))
      (.case (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename insBX hl₂) (HasType.rename insBY hr₂))
  have split := slot_sum_split_proof i hi hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv i) =
      .case (.bv y) (.case (.bv i.succ) l₁ r₁) (.case (.bv i.succ) l₂ r₂) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l₁).trans (LetCase.LocallyNameless.Tm.bsubst_id l₁)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r₁).trans (LetCase.LocallyNameless.Tm.bsubst_id r₁)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l₂).trans (LetCase.LocallyNameless.Tm.bsubst_id l₂)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r₂).trans (LetCase.LocallyNameless.Tm.bsubst_id r₂)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at split
  have eqL : LetCase.LocallyNameless.Tm.instantiate K.underBinder (.inl (.bv 0)) =
      .case (.bv y.succ)
        (.case (.inl (.bv 1)) (l₁.rename (((BoundCtx.Renaming.succ Δ X).up A).up X).toFun)
          (r₁.rename (((BoundCtx.Renaming.succ Δ X).up A).up Y).toFun))
        (.case (.inl (.bv 1)) (l₂.rename (((BoundCtx.Renaming.succ Δ X).up B).up X).toFun)
          (r₂.rename (((BoundCtx.Renaming.succ Δ X).up B).up Y).toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder, LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l₁).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ l₁)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r₁).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ r₁)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l₂).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ l₂)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r₂).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ r₂)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
  have eqR : LetCase.LocallyNameless.Tm.instantiate K.underBinder (.inr (.bv 0)) =
      .case (.bv y.succ)
        (.case (.inr (.bv 1)) (l₁.rename (((BoundCtx.Renaming.succ Δ Y).up A).up X).toFun)
          (r₁.rename (((BoundCtx.Renaming.succ Δ Y).up A).up Y).toFun))
        (.case (.inr (.bv 1)) (l₂.rename (((BoundCtx.Renaming.succ Δ Y).up B).up X).toFun)
          (r₂.rename (((BoundCtx.Renaming.succ Δ Y).up B).up Y).toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder, LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l₁).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ l₁)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r₁).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ r₁)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
    · congr 1
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l₂).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ l₂)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
      · refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r₂).trans (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ r₂)
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => rfl) i
  rw [eqL, eqR] at split
  have hs : HasType Φ Γ₀ Δ (.bv i) (.coprod X Y) := hi ▸ .bv
  exact split.trans (Equiv.case (.refl hs)
    (Equiv.case (.refl (slot_typed (Γ := Δ.snoc X) y.succ hy)) (sum_arm_inl_proof hl₁ hr₁)
      (sum_arm_inl_proof hl₂ hr₂))
    (Equiv.case (.refl (slot_typed (Γ := Δ.snoc Y) y.succ hy)) (sum_arm_inr_proof hl₁ hr₁)
      (sum_arm_inr_proof hl₂ hr₂)))

end CaseSlot
/-- A native equation between terms equal to the given ones. -/
theorem equiv_cast [HasTy Φ (Ty α)] {k : Nat} {Γ : BoundCtx (Ty α) k} {C : Ty α}
    {x y x' y' : LetCase.LocallyNameless.Tm Empty Φ k} (h : Equiv false Γ₀ Γ x y C) (ex : x = x') (ey : y = y') :
    Equiv false Γ₀ Γ x' y' C := by
  subst ex
  subst ey
  exact h

/-! ## A case on a stored sum slot after a finite prefix

A prefix of requests and pattern lets in front of a case on a stored slot
of sum type is natively equal to the case in front of the two
specializations of the prefix. One step of the induction on the prefix
uses the equation that moves a case in front of a binding, or the equation
that moves a pattern let out of both arms of a case. No two requests are
exchanged. -/

section Prefix

variable [TaggedSignature α Φ]

omit [TaggedSignature α Φ] in
/-- A typed let has a typed bound term and a typed body. -/
theorem hasType_let_inv [HasTy Φ (Ty α)] {k : Nat} {β : BoundCtx (Ty α) k} {a : LetCase.LocallyNameless.Tm Empty Φ k}
    {b : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} {C : Ty α} (h : HasType Φ Γ₀ β (.let₁ a b) C) :
    ∃ A : Ty α, HasType Φ Γ₀ β a A ∧ HasType Φ Γ₀ (β.snoc A) b C := by
  cases h with
  | let₁ ha hb => exact ⟨_, ha, hb⟩

omit [TaggedSignature α Φ] in
/-- A typed case has a typed scrutinee and typed arms. -/
theorem hasType_case_inv [HasTy Φ (Ty α)] {k : Nat} {β : BoundCtx (Ty α) k} {a : LetCase.LocallyNameless.Tm Empty Φ k}
    {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} {C : Ty α} (h : HasType Φ Γ₀ β (.case a l r) C) :
    ∃ A B : Ty α, HasType Φ Γ₀ β a (.coprod A B) ∧ HasType Φ Γ₀ (β.snoc A) l C ∧
      HasType Φ Γ₀ (β.snoc B) r C := by
  cases h with
  | case ha hl hr => exact ⟨_, _, ha, hl, hr⟩

omit [TaggedSignature α Φ] in
/-- A typed pattern let has a typed scrutinee and a typed body. -/
theorem hasType_pair_inv [HasTy Φ (Ty α)] {k : Nat} {β : BoundCtx (Ty α) k} {a : LetCase.LocallyNameless.Tm Empty Φ k}
    {c : LetCase.LocallyNameless.Tm Empty Φ (k + 2)} {C : Ty α} (h : HasType Φ Γ₀ β (.let₂ a c) C) :
    ∃ A B : Ty α, HasType Φ Γ₀ β a (.product A B) ∧ HasType Φ Γ₀ ((β.snoc A).snoc B) c C := by
  cases h with
  | let₂ ha hc => exact ⟨_, _, ha, hc⟩

/-- A request is typed at its reply type. -/
theorem hasType_op_type {k : Nat} {β : BoundCtx (Ty α) k} {g : Φ} {a : LetCase.LocallyNameless.Tm Empty Φ k} {A : Ty α}
    (h : HasType Φ Γ₀ β (.op g a) A) : A = tagsTy (replyTags g) := by
  cases h
  rfl

omit [TaggedSignature α Φ] in
/-- A slot is typed at its type in the context. -/
theorem hasType_bv_type [HasTy Φ (Ty α)] {k : Nat} {β : BoundCtx (Ty α) k} {i : Fin k} {A : Ty α}
    (h : HasType Φ Γ₀ β (.bv i) A) : A = β.get i := by
  cases h
  rfl

/-- The finite-prefix equation. A prefix followed by a case on a stored
slot of sum type is natively equal to the case on that slot followed by
the specialization of the prefix in each arm. -/
theorem deferred_equiv_proof {X Y C : Ty α} : {k : Nat} → {Γ : BoundCtx (Ty α) k} → {s : Fin k} →
    {t : LetCase.LocallyNameless.Tm Empty Φ k} → {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} → (w : Deferred X Y Γ s t l r) →
    HasType Φ Γ₀ (Γ.snoc X) l C → HasType Φ Γ₀ (Γ.snoc Y) r C →
    Equiv false Γ₀ Γ t (.case (.bv s) l r) C
  | _, _, s, _, _, _, .here hs _ _, hl, hr => .refl (.case (slot_typed s hs) hl hr)
  | _, Γ, s, _, _, _, .ask (l := l) (r := r) g argument rest, hl, hr => by
    let Z : Ty α := tagsTy (replyTags g)
    have hs : Γ.get s = .coprod X Y := rest.slot
    have hE : HasType Φ Γ₀ Γ (.op g (argTerm argument)) Z :=
      (Derivation.op (f := g) (argTyping argument)).toHasType
    obtain ⟨Al, hEl, hbl⟩ := hasType_let_inv hl
    obtain ⟨Ar, hEr, hbr⟩ := hasType_let_inv hr
    obtain rfl := hasType_op_type hEl
    obtain rfl := hasType_op_type hEr
    have hl' : HasType Φ Γ₀ ((Γ.snoc Z).snoc X) l C := by
      have h := HasType.rename (swapRenaming Γ X Z) hbl
      rwa [swap_swap_rename] at h
    have hr' : HasType Φ Γ₀ ((Γ.snoc Z).snoc Y) r C := by
      have h := HasType.rename (swapRenaming Γ Y Z) hbr
      rwa [swap_swap_rename] at h
    have ih := deferred_equiv_proof rest hl' hr'
    have comm := let_case_comm_proof s hs hE hl' hr'
    exact (Equiv.let₁ (.refl hE) ih).trans (equiv_cast comm rfl
      (congrArg₂ (fun a b => LetCase.LocallyNameless.Tm.case (.bv s)
          (.let₁ (.op g a) (l.rename (swapRenaming Γ Z X).toFun))
          (.let₁ (.op g b) (r.rename (swapRenaming Γ Z Y).toFun)))
        (argTerm_rename argument (BoundCtx.Renaming.succ Γ X))
        (argTerm_rename argument (BoundCtx.Renaming.succ Γ Y))))
  | _, Γ, s, _, _, _, .unpack (A := A) (B := B) (l := l) (r := r) x rest, hl, hr => by
    have hs : Γ.get s = .coprod X Y := rest.slot
    obtain ⟨Al, Bl, hvl, hbl⟩ := hasType_pair_inv hl
    obtain ⟨Ar, Br, hvr, hbr⟩ := hasType_pair_inv hr
    have el : Ty.product Al Bl = Ty.product A B := (hasType_bv_type hvl).trans x.2
    have er : Ty.product Ar Br = Ty.product A B := (hasType_bv_type hvr).trans x.2
    obtain ⟨hAl, hBl⟩ := Ty.product.inj el
    obtain ⟨hAr, hBr⟩ := Ty.product.inj er
    subst hAl hBl hAr hBr
    have hl' : HasType Φ Γ₀ (((Γ.snoc Ar).snoc Br).snoc X) l C := by
      have h : HasType Φ Γ₀ (((Γ.snoc Ar).snoc Br).snoc X) ((l.rename beforePair).rename afterPair) C :=
        HasType.rename (afterPairRenaming Γ X Ar Br) hbl
      rwa [before_after_rename] at h
    have hr' : HasType Φ Γ₀ (((Γ.snoc Ar).snoc Br).snoc Y) r C := by
      have h : HasType Φ Γ₀ (((Γ.snoc Ar).snoc Br).snoc Y) ((r.rename beforePair).rename afterPair) C :=
        HasType.rename (afterPairRenaming Γ Y Ar Br) hbr
      rwa [before_after_rename] at h
    have ih := deferred_equiv_proof rest hl' hr'
    have comm := case_pair_comm_proof s x.1 hs x.2 hbl hbr
    exact (Equiv.let₂ (.refl (slot_typed x.1 x.2)) ih).trans (equiv_cast comm.symm
      (congrArg₂ (fun a b => LetCase.LocallyNameless.Tm.let₂ (.bv x.1) (.case (.bv s.succ.succ) a b))
        (before_after_rename l) (before_after_rename r)) rfl)
  | _, Γ, s, _, _, _, .split (l₁ := l₁) (r₁ := r₁) (l₂ := l₂) (r₂ := r₂) y left right, hl, hr => by
    have hs : Γ.get s = .coprod X Y := left.slot
    obtain ⟨Al, Bl, hvl, hl₁', hl₂'⟩ := hasType_case_inv hl
    obtain ⟨Ar, Br, hvr, hr₁', hr₂'⟩ := hasType_case_inv hr
    obtain ⟨hAl, hBl⟩ := Ty.coprod.inj ((hasType_bv_type hvl).trans y.2)
    obtain ⟨hAr, hBr⟩ := Ty.coprod.inj ((hasType_bv_type hvr).trans y.2)
    subst hAl hBl hAr hBr
    have hl₁ : HasType Φ Γ₀ ((Γ.snoc Ar).snoc X) l₁ C := by
      have h := HasType.rename (swapRenaming Γ X Ar) hl₁'
      rwa [swap_swap_rename] at h
    have hl₂ : HasType Φ Γ₀ ((Γ.snoc Br).snoc X) l₂ C := by
      have h := HasType.rename (swapRenaming Γ X Br) hl₂'
      rwa [swap_swap_rename] at h
    have hr₁ : HasType Φ Γ₀ ((Γ.snoc Ar).snoc Y) r₁ C := by
      have h := HasType.rename (swapRenaming Γ Y Ar) hr₁'
      rwa [swap_swap_rename] at h
    have hr₂ : HasType Φ Γ₀ ((Γ.snoc Br).snoc Y) r₂ C := by
      have h := HasType.rename (swapRenaming Γ Y Br) hr₂'
      rwa [swap_swap_rename] at h
    exact (Equiv.case (.refl (slot_typed y.1 y.2)) (deferred_equiv_proof left hl₁ hr₁)
      (deferred_equiv_proof right hl₂ hr₂)).trans (case_case_comm_proof s y.1 hs y.2 hl₁ hr₁ hl₂ hr₂)

end Prefix

/-! ## Moving a binding or a case under the unpackings of a stack

The unpackings of every tuple of a stack move in front of a binding that
moves single pattern lets, and out of both arms of a case, by induction on
the stack. The stack has any depth. -/

section Stack

variable [HasTy Φ (Ty α)]

/-- The unpackings of a stack are typed when the slots have the tuple
types. -/
theorem unpackStack_typed_proof : (stack : List (List α)) → {k : Nat} → {Ω : BoundCtx (Ty α) k} →
    (H : Holds Ω stack) → {u : LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack)} → {C : Ty α} →
    HasType Φ Γ₀ (stackCtx stack Ω) u C → HasType Φ Γ₀ Ω (unpackStack stack H u) C
  | [], _, _, _, _, _, h => h
  | atoms :: stack, _, Ω, .cons top older, _, _, h =>
    unpackStack_typed_proof stack older
      (unpackAt_typed_proof atoms ((weakenStack stack Ω).toFun top.1)
        (((weakenStack stack Ω).typed top.1).trans top.2) h)

/-- The unpackings of a stack preserve native equations. -/
theorem unpackStack_congr_proof : (stack : List (List α)) → {k : Nat} → {Ω : BoundCtx (Ty α) k} →
    (H : Holds Ω stack) → {u v : LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack)} → {C : Ty α} →
    Equiv false Γ₀ (stackCtx stack Ω) u v C →
    Equiv false Γ₀ Ω (unpackStack stack H u) (unpackStack stack H v) C
  | [], _, _, _, _, _, _, h => h
  | atoms :: stack, _, Ω, .cons top older, _, _, _, h =>
    unpackStack_congr_proof stack older
      (unpackAt_congr_proof atoms ((weakenStack stack Ω).toFun top.1)
        (((weakenStack stack Ω).typed top.1).trans top.2) h)

/-- A pattern let on a pair slot is an action on terms that moves a pattern
let on an older pair slot to its front. -/
theorem pair_frame_proof {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {A B : Ty α} (i : Fin m)
    (h : Ω.get i = .product A B) :
    PairFrame (Φ := Φ) C Ω [A, B] (fun ω u => .let₂ (.bv (ω.toFun i)) u) where
  typed ω _ hu := .let₂ (slot_typed (ω.toFun i) ((ω.typed i).trans h)) hu
  comm ω j A' B' hj body hBody :=
    equiv_cast (let_pair_pair_comm_proof (ω.toFun i) j ((ω.typed i).trans h) hj hBody) rfl
      (congrArg (fun r : BoundCtx.Renaming _ _ =>
          LetCase.LocallyNameless.Tm.let₂ (.bv j) (.let₂ (.bv (ω.toFun i).succ.succ) (body.rename r.toFun)))
        (pairPastTele_pair _ A B A' B').symm)

/-- Binding by a term is an action on terms that moves a pattern let on an
older pair slot to its front. -/
theorem let_frame_proof {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {X : Ty α}
    (E : LetCase.LocallyNameless.Tm Empty Φ m) (hE : HasType Φ Γ₀ Ω E X) :
    PairFrame C Ω [X] (fun ω u => .let₁ (E.rename ω.toFun) u) where
  typed ω _ hu := .let₁ (HasType.rename ω hE) hu
  comm ω j A B hj body hBody := by
    have h := let_pair_comm_proof j hj (HasType.rename ω hE) hBody
    exact equiv_cast h rfl (congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv j))
      (congrArg₂ LetCase.LocallyNameless.Tm.let₁ (LetCase.LocallyNameless.Tm.rename_comp _ _ E)
        (congrArg (fun r : BoundCtx.Renaming _ _ => body.rename r.toFun) (pairPastTele_single _ X A B).symm)))

/-- Unpacking a tuple slot is an action on terms that moves a pattern let
on an older pair slot to its front. -/
theorem unpack_frame_proof {C : Ty α} (atoms : List α) {m : Nat} {Ω : BoundCtx (Ty α) m} (i : Fin m)
    (h : Ω.get i = tupleTy atoms) :
    PairFrame (Φ := Φ) C Ω (pairsTele atoms) (fun ω u => unpackAt atoms (ω.toFun i) u) where
  typed ω _ hu := unpackAt_typed_proof atoms (ω.toFun i) ((ω.typed i).trans h) hu
  comm ω j _ _ hj _ hBody := unpack_pair_comm_proof atoms (ω.toFun i) j ((ω.typed i).trans h) hj hBody

/-- The unpackings of every tuple of a stack move in front of an action on
terms that moves single pattern lets. -/
theorem stack_out_proof {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (frame : PairFrame C Ω tel term) :
    (stack : List (List α)) → {k : Nat} → {Ω' : BoundCtx (Ty α) k} → (ω : BoundCtx.Renaming Ω Ω') →
    (H : Holds Ω' stack) → {u : LetCase.LocallyNameless.Tm Empty Φ (stackSize (teleSize k tel) stack)} →
    HasType Φ Γ₀ (stackCtx stack (extendCtx Ω' tel)) u C →
    Equiv false Γ₀ Ω' (term ω (unpackStack stack (H.rename (weakenTele Ω' tel)) u))
      (unpackStack stack H (term (ω.comp (weakenStack stack Ω'))
        (u.rename (swapStack stack Ω' tel).toFun))) C
  | [], _, Ω', ω, _, u, hu =>
    Eq.subst (motive := fun x => Equiv false Γ₀ Ω' (term ω u)
      (term (ω.comp (weakenStack ([] : List (List α)) Ω')) x) C)
      (LetCase.LocallyNameless.Tm.rename_id u).symm (.refl (frame.typed ω hu))
  | atoms :: stack, k, Ω', ω, .cons top older, u, hu => by
    let Ω₁ := stackCtx stack Ω'
    let j := (weakenStack stack Ω').toFun top.1
    have hj : Ω₁.get j = tupleTy atoms := ((weakenStack stack Ω').typed top.1).trans top.2
    let i₀ := (weakenStack stack (extendCtx Ω' tel)).toFun ((weakenTele Ω' tel).toFun top.1)
    have hi₀ : (stackCtx stack (extendCtx Ω' tel)).get i₀ = tupleTy atoms :=
      ((weakenStack stack (extendCtx Ω' tel)).typed _).trans
        (((weakenTele Ω' tel).typed top.1).trans top.2)
    have ih := stack_out_proof frame stack ω older (unpackAt_typed_proof atoms i₀ hi₀ hu)
    have idx : (swapStack stack Ω' tel).toFun i₀ = (weakenTele Ω₁ tel).toFun j :=
      congrArg (fun r : BoundCtx.Renaming Ω' _ => r.toFun top.1) (swapStack_weakenTele stack Ω' tel)
    have moved : (unpackAt atoms i₀ u).rename (swapStack stack Ω' tel).toFun =
        unpackAt atoms ((weakenTele Ω₁ tel).toFun j)
          (u.rename (upTele (swapStack stack Ω' tel) (pairsTele atoms)).toFun) :=
      (unpackAt_rename (Φ := Φ) atoms (swapStack stack Ω' tel) i₀ u).trans
        (congrArg (fun i => unpackAt atoms i
          (u.rename (upTele (swapStack stack Ω' tel) (pairsTele atoms)).toFun)) idx)
    have hu₁ := HasType.rename (upTele (swapStack stack Ω' tel) (pairsTele atoms)) hu
    have out := unpack_out_proof frame atoms (ω.comp (weakenStack stack Ω')) j hj hu₁
    exact (equiv_cast ih rfl (congrArg (fun z => unpackStack stack older
        (term (ω.comp (weakenStack stack Ω')) z)) moved)).trans
      (equiv_cast (unpackStack_congr_proof stack older out) rfl
        (congrArg (fun z => unpackStack stack older (unpackAt atoms j
            (term (ω.comp (weakenStack (atoms :: stack) Ω')) z)))
          (LetCase.LocallyNameless.Tm.rename_comp (upTele (swapStack stack Ω' tel) (pairsTele atoms)).toFun
            (swapTeles Ω₁ tel (pairsTele atoms)).toFun u)))

/-- The unpackings of every tuple of a stack, done in both arms of a case
on a slot, move in front of the case. The case keeps its scrutinee. -/
theorem case_stack_out_proof {C : Ty α} : (stack : List (List α)) → {k : Nat} → {Γ : BoundCtx (Ty α) k} →
    (i : Fin k) → {X Y : Ty α} → Γ.get i = .coprod X Y → (H : Holds Γ stack) →
    {l r : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1) stack)} →
    HasType Φ Γ₀ (stackCtx stack (Γ.snoc X)) l C → HasType Φ Γ₀ (stackCtx stack (Γ.snoc Y)) r C →
    Equiv false Γ₀ Γ
      (.case (.bv i) (unpackStack stack (H.rename (weakenTele Γ [X])) l)
        (unpackStack stack (H.rename (weakenTele Γ [Y])) r))
      (unpackStack stack H (.case (.bv ((weakenStack stack Γ).toFun i))
        (l.rename (swapStack stack Γ [X]).toFun) (r.rename (swapStack stack Γ [Y]).toFun))) C
  | [], _, Γ, i, X, Y, hi, _, l, r, hl, hr =>
    Equiv.case (.refl (slot_typed i hi))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc X) l x C) (LetCase.LocallyNameless.Tm.rename_id l).symm (.refl hl))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc Y) r x C) (LetCase.LocallyNameless.Tm.rename_id r).symm (.refl hr))
  | atoms :: stack, k, Γ, i, X, Y, hi, .cons top older, l, r, hl, hr => by
    let Γ₁ := stackCtx stack Γ
    let j := (weakenStack stack Γ).toFun top.1
    let wi := (weakenStack stack Γ).toFun i
    have hj : Γ₁.get j = tupleTy atoms := ((weakenStack stack Γ).typed top.1).trans top.2
    have hwi : Γ₁.get wi = .coprod X Y := ((weakenStack stack Γ).typed i).trans hi
    let iX := (weakenStack stack (Γ.snoc X)).toFun ((weakenTele Γ [X]).toFun top.1)
    let iY := (weakenStack stack (Γ.snoc Y)).toFun ((weakenTele Γ [Y]).toFun top.1)
    have hiX : (stackCtx stack (Γ.snoc X)).get iX = tupleTy atoms :=
      ((weakenStack stack (Γ.snoc X)).typed _).trans (((weakenTele Γ [X]).typed top.1).trans top.2)
    have hiY : (stackCtx stack (Γ.snoc Y)).get iY = tupleTy atoms :=
      ((weakenStack stack (Γ.snoc Y)).typed _).trans (((weakenTele Γ [Y]).typed top.1).trans top.2)
    have ih := case_stack_out_proof (C := C) stack i hi older
      (unpackAt_typed_proof atoms iX hiX hl) (unpackAt_typed_proof atoms iY hiY hr)
    have idxX : (swapStack stack Γ [X]).toFun iX = j.succ :=
      congrArg (fun r : BoundCtx.Renaming Γ _ => r.toFun top.1) (swapStack_weakenTele stack Γ [X])
    have idxY : (swapStack stack Γ [Y]).toFun iY = j.succ :=
      congrArg (fun r : BoundCtx.Renaming Γ _ => r.toFun top.1) (swapStack_weakenTele stack Γ [Y])
    have movedX : (unpackAt atoms iX l).rename (swapStack stack Γ [X]).toFun =
        unpackAt atoms j.succ (l.rename (upTele (swapStack stack Γ [X]) (pairsTele atoms)).toFun) :=
      (unpackAt_rename (Φ := Φ) atoms (swapStack stack Γ [X]) iX l).trans
        (congrArg (fun i => unpackAt atoms i
          (l.rename (upTele (swapStack stack Γ [X]) (pairsTele atoms)).toFun)) idxX)
    have movedY : (unpackAt atoms iY r).rename (swapStack stack Γ [Y]).toFun =
        unpackAt atoms j.succ (r.rename (upTele (swapStack stack Γ [Y]) (pairsTele atoms)).toFun) :=
      (unpackAt_rename (Φ := Φ) atoms (swapStack stack Γ [Y]) iY r).trans
        (congrArg (fun i => unpackAt atoms i
          (r.rename (upTele (swapStack stack Γ [Y]) (pairsTele atoms)).toFun)) idxY)
    have out := case_unpack_out_proof (C := C) atoms (Γ := Γ₁) wi j hwi hj
      (HasType.rename (upTele (swapStack stack Γ [X]) (pairsTele atoms)) hl)
      (HasType.rename (upTele (swapStack stack Γ [Y]) (pairsTele atoms)) hr)
    exact (equiv_cast ih rfl (congrArg₂ (fun x y => unpackStack stack older
        (LetCase.LocallyNameless.Tm.case (.bv wi) x y)) movedX movedY)).trans
      (equiv_cast (unpackStack_congr_proof stack older out) rfl
        (congrArg₂ (fun x y => unpackStack stack older (unpackAt atoms j
            (LetCase.LocallyNameless.Tm.case (.bv ((weakenTele Γ₁ (pairsTele atoms)).toFun wi)) x y)))
          (LetCase.LocallyNameless.Tm.rename_comp (upTele (swapStack stack Γ [X]) (pairsTele atoms)).toFun
            (swapTeles Γ₁ [X] (pairsTele atoms)).toFun l)
          (LetCase.LocallyNameless.Tm.rename_comp (upTele (swapStack stack Γ [Y]) (pairsTele atoms)).toFun
            (swapTeles Γ₁ [Y] (pairsTele atoms)).toFun r)))

/-- The selection interchange for eager unpacking. Unpacking every tuple
of a stack with a selected tuple unpacked innermost is natively equal to
unpacking every tuple in the order of the stack, with the slots of the
selected unpacking moved to their place. The unpacking of the selected
tuple is exchanged with the unpacking of each newer tuple in turn. -/
theorem select_out_proof {C : Ty α} : {stack : List (List α)} → {atoms : List α} → {rest : List (List α)} →
    (sel : Select stack atoms rest) → {k : Nat} → {Ω : BoundCtx (Ty α) k} → (H : Holds Ω stack) →
    {u : LetCase.LocallyNameless.Tm Empty Φ (stackSize k (atoms :: rest))} →
    HasType Φ Γ₀ (stackCtx (atoms :: rest) Ω) u C →
    Equiv false Γ₀ Ω (unpackStack (atoms :: rest) (H.select sel) u)
      (unpackStack stack H (u.rename (selectRen sel Ω).toFun)) C
  | _, _, _, .here, _, Ω, .cons top older, u, hu =>
    Eq.subst (motive := fun x => Equiv false Γ₀ Ω (unpackStack _ (Holds.cons top older) u)
      (unpackStack _ (Holds.cons top older) x) C)
      (LetCase.LocallyNameless.Tm.rename_id u).symm (.refl (unpackStack_typed_proof _ (.cons top older) hu))
  | _, atoms, _, @Select.there _ x stack _ rest sel, k, Ω, .cons topx older, u, hu => by
    let Ω₁ := stackCtx rest Ω
    let j := (weakenStack rest Ω).toFun (older.pick sel).1
    let i := (weakenStack rest Ω).toFun topx.1
    have hj : Ω₁.get j = tupleTy atoms := ((weakenStack rest Ω).typed _).trans (older.pick sel).2
    have hi : Ω₁.get i = tupleTy x := ((weakenStack rest Ω).typed _).trans topx.2
    -- exchange the unpacking of the selected tuple with that of the newest tuple
    have out := unpack_out_proof (unpack_frame_proof (C := C) x (Ω := Ω₁) i hi) atoms
      (BoundCtx.Renaming.id Ω₁) j hj hu
    let i₂ := (weakenTele Ω₁ (pairsTele atoms)).toFun i
    have hi₂ : (stackCtx (atoms :: rest) Ω).get i₂ = tupleTy x :=
      ((weakenTele Ω₁ (pairsTele atoms)).typed i).trans hi
    have hu₂ : HasType Φ Γ₀ (stackCtx (atoms :: rest) Ω)
        (unpackAt x i₂ (u.rename (swapTeles Ω₁ (pairsTele x) (pairsTele atoms)).toFun)) C :=
      unpackAt_typed_proof x i₂ hi₂ (HasType.rename (swapTeles Ω₁ (pairsTele x) (pairsTele atoms)) hu)
    -- select among the older tuples
    have ih := select_out_proof (C := C) sel older hu₂
    have idx : (selectRen sel Ω).toFun i₂ = (weakenStack stack Ω).toFun topx.1 :=
      congrArg (fun r : BoundCtx.Renaming Ω _ => r.toFun topx.1) (selectRen_weaken sel Ω)
    have moved : (unpackAt x i₂ (u.rename (swapTeles Ω₁ (pairsTele x) (pairsTele atoms)).toFun)).rename
        (selectRen sel Ω).toFun =
        unpackAt x ((weakenStack stack Ω).toFun topx.1)
          (u.rename (selectRen (Select.there (x := x) sel) Ω).toFun) :=
      ((unpackAt_rename (Φ := Φ) x (selectRen sel Ω) i₂ _).trans
        (congrArg (fun l => unpackAt x l ((u.rename (swapTeles Ω₁ (pairsTele x) (pairsTele atoms)).toFun).rename
          (upTele (selectRen sel Ω) (pairsTele x)).toFun)) idx)).trans
        (congrArg (unpackAt x ((weakenStack stack Ω).toFun topx.1))
          (LetCase.LocallyNameless.Tm.rename_comp (swapTeles Ω₁ (pairsTele x) (pairsTele atoms)).toFun
            (upTele (selectRen sel Ω) (pairsTele x)).toFun u))
    exact (unpackStack_congr_proof rest (older.drop sel) out).trans
      (equiv_cast ih rfl (congrArg (fun z => unpackStack stack older z) moved))

end Stack

/-! ## Binding under a pending tuple

A binding in front of a pending tuple is moved under the full unpacking of
the tuple. The binding is given by its native account: its action on terms
and the equation that moves a pattern let on an older pair slot in front
of it. That equation is used once for each pattern let of the unpacking. -/

section Push

variable [TaggedSignature α Φ]

/-- The native account of a way to bind a telescope, taken after a
renaming of the base context. -/
theorem framed_after_proof {m k : Nat} {Ω : BoundCtx (Ty α) m} {Ω₁ : BoundCtx (Ty α) k} {tel : List (Ty α)}
    {wrap : CaseTree.Wrap Φ L Ω tel}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (framed : wrap.Framed term) (ρ : BoundCtx.Renaming Ω Ω₁) :
    CaseTree.Wrap.Framed (L := L) (Ω := Ω₁) (tel := tel) (fun ω => wrap (ρ.comp ω))
      (fun ω => term (ρ.comp ω)) where
  spec ω _ r := framed.spec (ρ.comp ω) r
  comm ω j _ _ hj _ hBody := framed.comm (ρ.comp ω) j hj hBody

theorem pushed_spec_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.PushedSpec pending β tree := by
  induction tree with
  | ret exit payload => trivial
  | ask f argument reply ih => trivial
  | only atoms payload ih => trivial
  | split atoms next rest left right ihl ihr => trivial
  | unit body ih =>
    intro m Ω tel π wrap term framed
    have same : (CaseTree.pushed (CaseTree.unit body) π wrap).1 =
        term (BoundCtx.Renaming.succ Ω _) (_ : LetCase.LocallyNameless.Tm Empty Φ _) :=
      (framed.spec _ _).trans (congrArg _ (CaseTree.renamed_body_term body ((π.up _).comp (swapTele Ω tel _))))
    rw [← same]
    exact .refl (CaseTree.pushed (CaseTree.unit body) π wrap).2.typing.toHasType
  | atom a body ih =>
    intro m Ω tel π wrap term framed
    have same : (CaseTree.pushed (CaseTree.atom a body) π wrap).1 =
        term (BoundCtx.Renaming.succ Ω _) (_ : LetCase.LocallyNameless.Tm Empty Φ _) :=
      (framed.spec _ _).trans (congrArg _ (CaseTree.renamed_body_term body ((π.up _).comp (swapTele Ω tel _))))
    rw [← same]
    exact .refl (CaseTree.pushed (CaseTree.atom a body) π wrap).2.typing.toHasType
  | @pair _ Ξ L a b rest body later ih =>
    intro m Ω tel π wrap term framed
    let T : Ty α := tupleTy (a :: b :: rest)
    let T₂ : Ty α := tupleTy (b :: rest)
    let θ := (π.up T).comp (swapTele Ω tel T)
    let π₂ := ((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a))
    have typed : HasType Φ Γ₀ (((extendCtx (Ω.snoc T) tel).snoc (Ty.base a)).snoc T₂)
        (body.rename ((θ.up (Ty.base a)).up T₂).toFun) (packedExitType L) :=
      HasType.rename ((θ.up _).up _) later.typing.toHasType
    have comm := framed.comm (BoundCtx.Renaming.succ Ω T) (0 : Fin (m + 1)) rfl typed
    have zero : (weakenTele (Ω.snoc T) tel).toFun 0 = θ.toFun 0 :=
      (congrArg (fun r => r.toFun 0) (swapTele_weaken tel Ω T)).symm
    rw [zero] at comm
    have next := ih π₂ (fun ω => wrap ((pastPair Ω T (Ty.base a)).comp ω))
      (fun ω => term ((pastPair Ω T (Ty.base a)).comp ω)) (framed_after_proof framed (pastPair Ω T (Ty.base a)))
    have inner : (((π.up T).comp (swapTele Ω tel T)).up (Ty.base a)).comp (swapTele (Ω.snoc T) tel (Ty.base a)) =
        ((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a)) := by
      rw [← renaming_up_comp (π.up T) (swapTele Ω tel T) (Ty.base a)]
      rfl
    have e : ((θ.up (Ty.base a)).up T₂).comp (pairPastTele (Ω.snoc T) tel (Ty.base a) T₂) =
        (π₂.up T₂).comp (swapTele ((Ω.snoc T).snoc (Ty.base a)) tel T₂) := by
      show (((((π.up T).comp (swapTele Ω tel T)).up (Ty.base a)).up T₂).comp
        ((swapTele (Ω.snoc T) tel (Ty.base a)).up T₂)).comp
          (swapTele ((Ω.snoc T).snoc (Ty.base a)) tel T₂) = _
      rw [renaming_up_comp, inner]
    have moved : (body.rename ((θ.up (Ty.base a)).up T₂).toFun).rename
        (pairPastTele (Ω.snoc T) tel (Ty.base a) T₂).toFun =
        body.rename ((π₂.up T₂).comp (swapTele ((Ω.snoc T).snoc (Ty.base a)) tel T₂)).toFun :=
      (LetCase.LocallyNameless.Tm.rename_comp _ _ body).trans (congrArg (fun r => body.rename r.toFun) e)
    rw [moved] at comm
    exact comm.trans (Equiv.let₂ (.refl .bv) next)

/-- Binding a tuple by `E` and unpacking it has a native account. -/
theorem unpack_framed_proof (atoms : List α) {m : Nat} {Ω : BoundCtx (Ty α) m}
    (wrap : CaseTree.Wrap Φ L Ω (unpackTele atoms)) (E : LetCase.LocallyNameless.Tm Empty Φ m)
    (hE : HasType Φ Γ₀ Ω E (tupleTy atoms))
    (spec : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
      {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms))}
      (r : CaseTree .body (extendCtx Ω' (unpackTele atoms)) L u),
      (wrap ω r).1 = .let₁ (E.rename ω.toFun) (unpackAt atoms 0 u)) :
    wrap.Framed (fun ω u => .let₁ (E.rename ω.toFun) (unpackAt atoms 0 u)) where
  spec ω _ r := spec ω r
  comm ω j _ _ hj _ hBody := by
    have h := let_unpack_pair_comm_proof atoms j hj (HasType.rename ω hE) hBody
    rw [LetCase.LocallyNameless.Tm.rename_comp] at h
    exact h

end Push

/-! ## The native equation between a spelling and its normal form

Each head uses one native sequencing law. A bound head needs none. A pair
head uses the law that binds the scrutinee of a pattern let, and a case
head the law that binds the scrutinee of a case. In both, the body is
weakened past the bound reply. -/

section Spelled

variable [TaggedSignature α Φ]

/-- The normal-form equation at a case on a bound reply, from the equations
of its arms. It is shared by the case that directly follows its request and
by the case that is delayed across a prefix. -/
theorem split_opened_equiv {stack : List (List α)} {atoms nxt : List α} {more : List (List α)} {m : Nat}
    {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
    (left : SpelledStack (atoms :: stack) ((Δ.snoc (tagsTy (atoms :: nxt :: more))).snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: nxt :: more)) (tupleTy atoms)))) L l)
    (right : SpelledStackTags stack (nxt :: more) (Δ.snoc (tagsTy (atoms :: nxt :: more)))
      (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: nxt :: more)))) L r)
    {k : Nat} {Θ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming Δ Θ)
    (ihl : Equiv false Γ₀ ((Θ.snoc (tagsTy (atoms :: nxt :: more))).snoc (tupleTy atoms)) (l.rename ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms)).toFun)
      (unpackStack (atoms :: stack)
        ((Holds.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: nxt :: more)) (tupleTy atoms)))).rename ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms)))
        (left.opened ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))).1) (packedExitType L))
    (ihr : ∃ V : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1 + 1) stack),
      Equiv false Γ₀ ((Θ.snoc (tagsTy (atoms :: nxt :: more))).snoc (tagsTy (nxt :: more))) (r.rename ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tagsTy (nxt :: more))).toFun)
        (unpackStack stack (((holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: nxt :: more)))).rename (ρ.up (tagsTy (atoms :: nxt :: more)))).rename
          (weakenTele (Θ.snoc (tagsTy (atoms :: nxt :: more))) [tagsTy (nxt :: more)])) V) (packedExitType L) ∧
      HasType Φ Γ₀ (stackCtx stack ((Θ.snoc (tagsTy (atoms :: nxt :: more))).snoc (tagsTy (nxt :: more)))) V (packedExitType L) ∧
      V.rename (swapStack stack (Θ.snoc (tagsTy (atoms :: nxt :: more))) [tagsTy (nxt :: more)]).toFun = (right.opened (ρ.up (tagsTy (atoms :: nxt :: more)))).1) :
    ∃ U : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1) stack),
      Equiv false Γ₀ (Θ.snoc (tagsTy (atoms :: nxt :: more)))
        (.case (.bv 0) (l.rename ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms)).toFun) (r.rename ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tagsTy (nxt :: more))).toFun))
        (unpackStack stack ((holds.rename ρ).rename (weakenTele Θ [tagsTy (atoms :: nxt :: more)])) U) (packedExitType L) ∧
      HasType Φ Γ₀ (stackCtx stack (Θ.snoc (tagsTy (atoms :: nxt :: more)))) U (packedExitType L) ∧
      U.rename (swapStack stack Θ [tagsTy (atoms :: nxt :: more)]).toFun =
        ((SpelledStackTags.split atoms nxt more left right).opened ρ).1 := by
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    let X : Ty α := tupleTy atoms
    let Y : Ty α := tagsTy (nxt :: more)
    let Γ := Θ.snoc Rt
    let H' := (holds.rename ρ).rename (weakenTele Θ [Rt])
    let ρ₂ := (ρ.up Rt).up X
    -- the first arm
    have holdsL : (holds.rename (pastPair Δ Rt X)).rename ρ₂ = H'.rename (weakenTele Γ [X]) :=
      (Holds.rename_comp holds (pastPair Δ Rt X) ρ₂).trans
        ((congrArg (fun r => holds.rename r) (renaming_ext (ρ := (pastPair Δ Rt X).comp ρ₂)
          (π := (ρ.comp (weakenTele Θ [Rt])).comp (weakenTele Γ [X])) (fun _ => rfl))).trans
          ((Holds.rename_comp holds (ρ.comp (weakenTele Θ [Rt])) (weakenTele Γ [X])).symm.trans
            (congrArg (fun h => Holds.rename (weakenTele Γ [X]) h)
              (Holds.rename_comp holds ρ (weakenTele Θ [Rt])).symm)))
    let i₀ := (weakenStack stack (Γ.snoc X)).toFun 0
    have hNl := (left.opened ρ₂).2.typing.toHasType
    have hAl := unpackAt_typed_proof atoms i₀ ((weakenStack stack (Γ.snoc X)).typed 0) hNl
    have ihl' : Equiv false Γ₀ (Γ.snoc X) (_ : LetCase.LocallyNameless.Tm Empty Φ (k + 1 + 1))
        (unpackStack stack (H'.rename (weakenTele Γ [X])) (unpackAt atoms i₀ (left.opened ρ₂).1))
        (packedExitType L) :=
      equiv_cast ihl rfl (congrArg (fun h => unpackStack stack h
        (unpackAt atoms i₀ (left.opened ρ₂).1)) holdsL)
    -- the other arms
    obtain ⟨V, hflatR, hV, hopenR⟩ := ihr
    have holdsR : (holds.rename (BoundCtx.Renaming.succ Δ Rt)).rename (ρ.up Rt) = H' :=
      (Holds.rename_comp holds (BoundCtx.Renaming.succ Δ Rt) (ρ.up Rt)).trans
        ((congrArg (fun r => holds.rename r) (renaming_ext (ρ := (BoundCtx.Renaming.succ Δ Rt).comp (ρ.up Rt))
          (π := ρ.comp (weakenTele Θ [Rt])) (fun _ => rfl))).trans
          (Holds.rename_comp holds ρ (weakenTele Θ [Rt])).symm)
    have ihr' : Equiv false Γ₀ (Γ.snoc Y) (_ : LetCase.LocallyNameless.Tm Empty Φ (k + 1 + 1))
        (unpackStack stack (H'.rename (weakenTele Γ [Y])) V) (packedExitType L) :=
      equiv_cast hflatR rfl (congrArg (fun h => unpackStack stack (Holds.rename (weakenTele Γ [Y]) h) V) holdsR)
    -- the case
    have out := case_stack_out_proof (C := packedExitType L) stack (Γ := Γ) (X := X) (Y := Y) 0 rfl H' hAl hV
    have index : (swapStack stack Θ [Rt]).toFun ((weakenStack stack Γ).toFun 0) =
        (0 : Fin (stackSize k stack + 1)) :=
      congrArg (fun r : BoundCtx.Renaming Γ _ => r.toFun 0) (swapStack_weaken stack Θ [Rt])
    refine ⟨_, (Equiv.case (.refl (.bv (ι := (0 : Fin (k + 1))))) ihl' ihr').trans out,
      .case (slot_typed _ ((weakenStack stack Γ).typed 0))
        (HasType.rename (swapStack stack Γ [X]) hAl) (HasType.rename (swapStack stack Γ [Y]) hV), ?_⟩
    show LetCase.LocallyNameless.Tm.case (.bv ((swapStack stack Θ [Rt]).toFun ((weakenStack stack Γ).toFun 0)))
      (LetCase.LocallyNameless.Tm.rename ((swapStack stack Θ [Rt]).up X).toFun _)
      (LetCase.LocallyNameless.Tm.rename ((swapStack stack Θ [Rt]).up Y).toFun _) = _
    refine congr (congr (congrArg (fun i => LetCase.LocallyNameless.Tm.case (.bv i)) index) ?_) ?_
    · -- the first arm of the normal form
      have idx : (swapStack stack Θ [Rt, X]).toFun i₀ = (0 : Fin (stackSize k stack + 1 + 1)) :=
        congrArg (fun r : BoundCtx.Renaming (Γ.snoc X) _ => r.toFun 0) (swapStack_weaken stack Θ [Rt, X])
      exact ((LetCase.LocallyNameless.Tm.rename_comp (swapStack stack Γ [X]).toFun ((swapStack stack Θ [Rt]).up X).toFun
          (unpackAt atoms i₀ (left.opened ρ₂).1)).trans
        (congrArg (fun r : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename r.toFun (unpackAt atoms i₀ (left.opened ρ₂).1))
          (swapStack_cons stack Θ Rt [X]).symm)).trans
        (((unpackAt_rename (Φ := Φ) atoms (swapStack stack Θ [Rt, X]) i₀ _).trans
          (congrArg (fun i => unpackAt atoms i ((left.opened ρ₂).1.rename
            (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms)).toFun)) idx)).trans
          (congrArg (unpackAt atoms (0 : Fin (stackSize k stack + 1 + 1)))
            (CaseTree.renamed_body_term (left.opened ρ₂).2
              (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms))).symm))
    · -- the other arms of the normal form
      have renamedTags : (CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          (right.opened (ρ.up Rt)).2 (swapStack stack Θ [Rt])).1 =
          (right.opened (ρ.up Rt)).1.rename (LetCase.LocallyNameless.Tm.up (swapStack stack Θ [Rt]).toFun) :=
        CaseTree.renamed_term (right.opened (ρ.up Rt)).2 (swapStack stack Θ [Rt])
      exact (congrArg (fun t => LetCase.LocallyNameless.Tm.rename ((swapStack stack Θ [Rt]).up Y).toFun t) hopenR).trans
        renamedTags.symm

mutual

theorem Spelled.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : Spelled β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    Equiv false Γ₀ γ (t.rename ρ.toFun) (d.normal ρ).1 (packedExitType L)
  | _, _, _, .ret exit payload, _, _, ρ => by
    have term : (exit.term (argTerm (Φ := Φ) payload)).rename ρ.toFun =
        exit.term (argTerm (payload.rename ρ)) := by
      rw [ExitAt.term_rename, argTerm_rename]
    rw [term]
    exact .refl (CaseTree.ret exit (payload.rename ρ)).typing.toHasType
  | _, _, _, .ask f argument head, _, γ, ρ => by
    have request : (LetCase.LocallyNameless.Tm.op f (argTerm (Φ := Φ) argument)).rename ρ.toFun =
        .op f (argTerm (argument.rename ρ)) := by
      simp only [LetCase.LocallyNameless.Tm.rename, argTerm_rename]
    have he : HasType Φ Γ₀ γ ((LetCase.LocallyNameless.Tm.op f (argTerm (Φ := Φ) argument)).rename ρ.toFun)
        (tagsTy (replyTags f)) := by
      rw [request]
      exact (Derivation.op (f := f) (argTyping (argument.rename ρ))).toHasType
    have h := head.normal_equiv ρ he
    rw [request] at h
    exact h
  | _, _, _, .chain c, _, _, ρ => c.opened_equiv ρ

theorem SpelledHead.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledHead tags e β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    HasType Φ Γ₀ γ (e.rename ρ.toFun) (tagsTy tags) →
    Equiv false Γ₀ γ (t.rename ρ.toFun) (.let₁ (e.rename ρ.toFun) (d.normal ρ).1) (packedExitType L)
  | _, _, _, _, _, .bind reply, _, _, ρ, he => Equiv.let₁ (.refl he) (reply.normal_equiv ρ)
  | _, _, _, e, _, .destruct (t := body) a b rest later, _, γ, ρ, he => by
    have typed : HasType Φ Γ₀ ((γ.snoc (.base a)).snoc (tupleTy (b :: rest)))
        (body.rename (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up ρ.toFun)))
        (packedExitType L) :=
      HasType.rename ((ρ.up _).up _) later.typing.toHasType
    have bind := Equiv.bindPair (pureEff := false) he typed
    have weaken : (body.rename (LetCase.LocallyNameless.Tm.up
        (LetCase.LocallyNameless.Tm.up ρ.toFun))).underTwoBinders =
          body.rename (LetCase.LocallyNameless.Tm.up
            (armRenaming ρ (tupleTy (a :: b :: rest)) (.base a)).toFun) := by
      rw [LetCase.LocallyNameless.Tm.underTwoBinders, LetCase.LocallyNameless.Tm.rename_comp]
      apply LetCase.LocallyNameless.Tm.rename_congr
      intro i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    rw [weaken] at bind
    exact bind.trans (Equiv.let₁ (.refl he) (Equiv.let₂ (.refl .bv) (later.normal_equiv (armRenaming ρ _ _))))
  | _, _, _, e, _, .branch (l := l) (r := r) atoms next rest left right, _, γ, ρ, he => by
    have hl : HasType Φ Γ₀ (γ.snoc (tupleTy atoms)) (l.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
        (packedExitType L) :=
      HasType.rename (ρ.up _) left.typing.toHasType
    have hr : HasType Φ Γ₀ (γ.snoc (tagsTy (next :: rest))) (r.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
        (packedExitType L) :=
      HasType.rename (ρ.up _) right.typing.toHasType
    have bind := Equiv.bindCase (pureEff := false) he hl hr
    have weaken (a : LetCase.LocallyNameless.Tm Empty Φ (_ + 1)) :
        (a.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)).underBinder =
          a.rename (LetCase.LocallyNameless.Tm.up
            (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))).toFun) := by
      rw [LetCase.LocallyNameless.Tm.underBinder, LetCase.LocallyNameless.Tm.rename_comp]
      apply LetCase.LocallyNameless.Tm.rename_congr
      intro i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [weaken, weaken] at bind
    exact bind.trans (Equiv.let₁ (.refl he) (Equiv.case (.refl .bv)
      (left.normal_equiv (ρ.comp (BoundCtx.Renaming.succ γ _)))
      (right.normal_equiv (ρ.comp (BoundCtx.Renaming.succ γ _)))))

theorem SpelledTags.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTags tags β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    Equiv false Γ₀ (γ.snoc (tagsTy tags)) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)) (d.normal ρ).1
      (packedExitType L)
  | _, _, _, _, .only _ payload, _, _, ρ => payload.normal_equiv ρ
  | _, _, _, _, .split _ _ _ left right, _, _, ρ =>
    Equiv.case (.refl .bv) (left.normal_equiv (ρ.up _)) (right.normal_equiv (ρ.up _))

theorem SpelledTuple.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    Equiv false Γ₀ (γ.snoc (tupleTy atoms)) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)) (d.normal ρ).1
      (packedExitType L)
  | _, _, _, _, .unit body, _, _, ρ => body.normal_equiv (ρ.up _)
  | _, _, _, _, .atom _ body, _, _, ρ => body.normal_equiv (ρ.up _)
  | _, _, _, _, .pair _ _ _ later, _, _, ρ =>
    Equiv.let₂ (.refl .bv) (later.normal_equiv ((ρ.up _).up _))
  | _, _, _, _, .hold _ chain, _, _, ρ => chain.opened_equiv (ρ.up _)

/-- A chain over a stack of packed tuples, renamed, is natively equal to
unpacking every tuple of the stack, oldest outermost, and then running the
body of the normal form. -/
theorem SpelledStack.opened_equiv : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledStack stack Δ holds L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Θ) →
    Equiv false Γ₀ Θ (t.rename ρ.toFun) (unpackStack stack (holds.rename ρ) (d.opened ρ).1)
      (packedExitType L)
  | _, _, _, _, _, .done body, _, _, ρ => body.normal_equiv ρ
  | _, _, _, .cons _ _, _, .unit next, _, _, ρ => next.opened_equiv ρ
  | _, _, _, .cons _ _, _, .atom next, _, _, ρ => next.opened_equiv ρ
  | (a :: b :: rest) :: stack, _, Δ, .cons top older, _, .step next, k, Θ, ρ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    let ρ₂ := (ρ.up A).up T
    have ih := next.opened_equiv ρ₂
    have holdsEq : (older.rename (pastPair Δ A T)).rename ρ₂ = (older.rename ρ).rename (weakenTele Θ [A, T]) :=
      (Holds.rename_comp older (pastPair Δ A T) ρ₂).trans
        ((congrArg (fun r => older.rename r) (renaming_ext (ρ := (pastPair Δ A T).comp ρ₂)
          (π := ρ.comp (weakenTele Θ [A, T])) (fun _ => rfl))).trans
          (Holds.rename_comp older ρ (weakenTele Θ [A, T])).symm)
    let i₀ := (weakenStack stack ((Θ.snoc A).snoc T)).toFun 0
    have hN := (next.opened ρ₂).2.typing.toHasType
    have hV := unpackAt_typed_proof (b :: rest) i₀ ((weakenStack stack ((Θ.snoc A).snoc T)).typed 0) hN
    have ih' : Equiv false Γ₀ ((Θ.snoc A).snoc T) (_ : LetCase.LocallyNameless.Tm Empty Φ (k + 1 + 1))
        (unpackStack stack ((older.rename ρ).rename (weakenTele Θ [A, T]))
          (unpackAt (b :: rest) i₀ (next.opened ρ₂).1)) (packedExitType L) :=
      equiv_cast ih rfl (congrArg (fun h => unpackStack stack h
        (unpackAt (b :: rest) i₀ (next.opened ρ₂).1)) holdsEq)
    have hx : Θ.get (ρ.toFun top.1) = .product A T := (ρ.typed top.1).trans top.2
    have out := stack_out_proof (pair_frame_proof (C := packedExitType L) (ρ.toFun top.1) hx) stack
      (BoundCtx.Renaming.id Θ) (older.rename ρ) hV
    have idx : (swapStack stack Θ [A, T]).toFun i₀ = (0 : Fin (stackSize k stack + 1 + 1)) :=
      congrArg (fun r : BoundCtx.Renaming ((Θ.snoc A).snoc T) _ => r.toFun 0) (swapStack_weaken stack Θ [A, T])
    have moved : (unpackAt (b :: rest) i₀ (next.opened ρ₂).1).rename (swapStack stack Θ [A, T]).toFun =
        unpackAt (b :: rest) (0 : Fin (stackSize k stack + 1 + 1))
          (CaseTree.renamed (pending := .body) (next.opened ρ₂).2
            (upTele (swapStack stack Θ [A, T]) (pairsTele (b :: rest)))).1 :=
      ((unpackAt_rename (Φ := Φ) (b :: rest) (swapStack stack Θ [A, T]) i₀ _).trans
        (congrArg (fun i => unpackAt (b :: rest) i ((next.opened ρ₂).1.rename
          (upTele (swapStack stack Θ [A, T]) (pairsTele (b :: rest))).toFun)) idx)).trans
        (congrArg (unpackAt (b :: rest) (0 : Fin (stackSize k stack + 1 + 1)))
          (CaseTree.renamed_body_term (next.opened ρ₂).2
            (upTele (swapStack stack Θ [A, T]) (pairsTele (b :: rest)))).symm)
    exact (Equiv.let₂ (.refl (slot_typed (ρ.toFun top.1) hx)) ih').trans
      (equiv_cast out rfl (congrArg (fun z => unpackStack stack (older.rename ρ)
        (LetCase.LocallyNameless.Tm.let₂ (.bv ((weakenStack stack Θ).toFun (ρ.toFun top.1))) z)) moved))
  | stack, _, Δ, holds, _, .ask g argument reply, k, Θ, ρ => by
    let Rt : Ty α := tagsTy (replyTags g)
    obtain ⟨U, hflat, hU, hopen⟩ := reply.opened_equiv ρ
    have hE : HasType Φ Γ₀ Θ (.op g (argTerm (argument.rename ρ))) Rt :=
      (Derivation.op (f := g) (argTyping (argument.rename ρ))).toHasType
    have out := stack_out_proof (let_frame_proof (C := packedExitType L) _ hE) stack
      (BoundCtx.Renaming.id Θ) (holds.rename ρ) hU
    have request₁ : (LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun =
        .op g (argTerm (argument.rename ρ)) := congrArg (LetCase.LocallyNameless.Tm.op g) (argTerm_rename argument ρ)
    have request₂ : (LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) (argument.rename ρ))).rename
        ((BoundCtx.Renaming.id Θ).comp (weakenStack stack Θ)).toFun =
        .op g (argTerm (argument.rename (ρ.comp (weakenStack stack Θ)))) :=
      congrArg (LetCase.LocallyNameless.Tm.op g) ((argTerm_rename (argument.rename ρ) (weakenStack stack Θ)).trans
        (congrArg argTerm (assembly_rename_comp argument ρ (weakenStack stack Θ))))
    exact equiv_cast ((Equiv.let₁ (.refl hE) hflat).trans
        (equiv_cast out
          (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ e (unpackStack stack ((holds.rename ρ).rename (weakenTele Θ [Rt])) U))
            (LetCase.LocallyNameless.Tm.rename_id _))
          (congrArg (fun z => unpackStack stack (holds.rename ρ) z) (congrArg₂ LetCase.LocallyNameless.Tm.let₁ request₂ hopen))))
      (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ e _) request₁.symm) rfl

  | _, _, _, holds, _, .pick sel next, _, Θ, ρ =>
    equiv_cast ((equiv_cast (next.opened_equiv ρ) rfl
        (congrArg (fun h => unpackStack _ h (next.opened ρ).1) (Holds.select_rename sel holds ρ).symm)).trans
        (select_out_proof (C := packedExitType L) sel (holds.rename ρ) (next.opened ρ).2.typing.toHasType))
      rfl (congrArg (unpackStack _ (holds.rename ρ))
        (CaseTree.renamed_body_term (next.opened ρ).2 (selectRen sel Θ)).symm)

/-- The same for the bound reply of a request, under its slot. The body is
given with the reply slot beneath the unpackings of the stack; renamed so
that the reply slot is newest it is the normal form of the reply. -/
theorem SpelledStackTags.opened_equiv : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    (d : SpelledStackTags stack tags Δ holds L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming Δ Θ) →
    ∃ U : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1) stack),
      Equiv false Γ₀ (Θ.snoc (tagsTy tags)) (t.rename (ρ.up (tagsTy tags)).toFun)
        (unpackStack stack ((holds.rename ρ).rename (weakenTele Θ [tagsTy tags])) U) (packedExitType L) ∧
      HasType Φ Γ₀ (stackCtx stack (Θ.snoc (tagsTy tags))) U (packedExitType L) ∧
      U.rename (swapStack stack Θ [tagsTy tags]).toFun = (d.opened ρ).1
  | stack, _, _, Δ, holds, _, .bind atoms next, k, Θ, ρ => by
    let X : Ty α := tupleTy atoms
    have ih := next.opened_equiv (ρ.up X)
    have holdsEq : (holds.rename (BoundCtx.Renaming.succ Δ X)).rename (ρ.up X) =
        (holds.rename ρ).rename (weakenTele Θ [X]) :=
      (Holds.rename_comp holds (BoundCtx.Renaming.succ Δ X) (ρ.up X)).trans
        ((congrArg (fun r => holds.rename r) (renaming_ext (ρ := (BoundCtx.Renaming.succ Δ X).comp (ρ.up X))
          (π := ρ.comp (weakenTele Θ [X])) (fun _ => rfl))).trans
          (Holds.rename_comp holds ρ (weakenTele Θ [X])).symm)
    let i₀ := (weakenStack stack (Θ.snoc X)).toFun 0
    have hN := (next.opened (ρ.up X)).2.typing.toHasType
    have idx : (swapStack stack Θ [X]).toFun i₀ = (0 : Fin (stackSize k stack + 1)) :=
      congrArg (fun r : BoundCtx.Renaming (Θ.snoc X) _ => r.toFun 0) (swapStack_weaken stack Θ [X])
    have ih' : Equiv false Γ₀ (Θ.snoc X) (_ : LetCase.LocallyNameless.Tm Empty Φ (k + 1))
        (unpackStack stack ((holds.rename ρ).rename (weakenTele Θ [X]))
          (unpackAt atoms i₀ (next.opened (ρ.up X)).1)) (packedExitType L) :=
      equiv_cast ih rfl (congrArg (fun h => unpackStack stack h
        (unpackAt atoms i₀ (next.opened (ρ.up X)).1)) holdsEq)
    exact ⟨unpackAt atoms i₀ (next.opened (ρ.up X)).1, ih',
      unpackAt_typed_proof atoms i₀ ((weakenStack stack (Θ.snoc X)).typed 0) hN,
      ((unpackAt_rename (Φ := Φ) atoms (swapStack stack Θ [X]) i₀ _).trans
        (congrArg (fun i => unpackAt atoms i ((next.opened (ρ.up X)).1.rename
          (upTele (swapStack stack Θ [X]) (pairsTele atoms)).toFun)) idx)).trans
        (congrArg (unpackAt atoms (0 : Fin (stackSize k stack + 1)))
          (CaseTree.renamed_body_term (next.opened (ρ.up X)).2
            (upTele (swapStack stack Θ [X]) (pairsTele atoms))).symm)⟩
  | _, _, _, _, _, _, .split _ _ _ left right, _, _, ρ =>
    split_opened_equiv left right ρ (left.opened_equiv _) (right.opened_equiv _)
  | _, _, _, _, _, _, .deferred atoms nxt more shape left right hl hr, _, _, ρ => by
    subst hl hr
    obtain ⟨U, h, hU, e⟩ := split_opened_equiv left right ρ (left.opened_equiv _) (right.opened_equiv _)
    exact ⟨U, ((deferred_equiv_proof shape left.typing.toHasType right.typing.toHasType).rename
      (ρ.up (tagsTy (atoms :: nxt :: more)))).trans h, hU, e⟩
  | _, tags, _, _, _, _, .later h argument arms, _, _, ρ => by
    obtain ⟨U, hflat, hU, hopen⟩ := arms.opened_equiv ρ (argument.rename (ρ.up (tagsTy tags)))
    exact ⟨U, equiv_cast hflat
      (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ (.op h e) _) (argTerm_rename argument (ρ.up (tagsTy tags))).symm) rfl,
      hU, hopen⟩

/-- A reply inspected after one later request `h`, with `h` asked in front
of it, is natively equal to the unpackings of the stack around a body that
cases on the reply first and asks `h` in each arm. The request is given
over the base context and the reply slot. -/
theorem SpelledLaterTags.opened_equiv : {stack : List (List α)} → {tags : List (List α)} → {h : Φ} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)} →
    (d : SpelledLaterTags stack tags h Δ holds L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming Δ Θ) → (arg : Assembly (Θ.snoc (tagsTy tags)) (instrSrc h)) →
    ∃ U : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1) stack),
      Equiv false Γ₀ (Θ.snoc (tagsTy tags))
        (.let₁ (.op h (argTerm arg)) (t.rename ((ρ.up (tagsTy tags)).up (tagsTy (replyTags h))).toFun))
        (unpackStack stack ((holds.rename ρ).rename (weakenTele Θ [tagsTy tags])) U) (packedExitType L) ∧
      HasType Φ Γ₀ (stackCtx stack (Θ.snoc (tagsTy tags))) U (packedExitType L) ∧
      U.rename (swapStack stack Θ [tagsTy tags]).toFun = (d.opened ρ arg).1
  | stack, _, h, _, Δ, holds, _, .only atoms next, k, Θ, ρ, arg => by
    let X : Ty α := tupleTy atoms
    let Rh : Ty α := tagsTy (replyTags h)
    obtain ⟨U₀, hflat₀, hU₀, hopen₀⟩ := next.opened_equiv (ρ.up X)
    have hE : HasType Φ Γ₀ (Θ.snoc X) (.op h (argTerm arg)) Rh :=
      (Derivation.op (f := h) (argTyping arg)).toHasType
    have holdsEq : (holds.rename (BoundCtx.Renaming.succ Δ X)).rename (ρ.up X) =
        (holds.rename ρ).rename (weakenTele Θ [X]) :=
      (Holds.rename_comp holds (BoundCtx.Renaming.succ Δ X) (ρ.up X)).trans
        ((congrArg (fun r => holds.rename r) (renaming_ext (ρ := (BoundCtx.Renaming.succ Δ X).comp (ρ.up X))
          (π := ρ.comp (weakenTele Θ [X])) (fun _ => rfl))).trans
          (Holds.rename_comp holds ρ (weakenTele Θ [X])).symm)
    let w := weakenStack (atoms :: stack) (Θ.snoc X)
    let s := swapStack (atoms :: stack) (Θ.snoc X) [Rh]
    let i₀ := (weakenStack stack (Θ.snoc X)).toFun 0
    let M : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1) (atoms :: stack)) :=
      .let₁ ((LetCase.LocallyNameless.Tm.op h (argTerm arg)).rename w.toFun) (U₀.rename s.toFun)
    have out := stack_out_proof (let_frame_proof (C := packedExitType L) _ hE) (atoms :: stack)
      (BoundCtx.Renaming.id (Θ.snoc X))
      ((Holds.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ X))).rename (ρ.up X)) hU₀
    have idx : (swapStack stack Θ [X]).toFun i₀ = (0 : Fin (stackSize k stack + 1)) :=
      congrArg (fun r : BoundCtx.Renaming (Θ.snoc X) _ => r.toFun 0) (swapStack_weaken stack Θ [X])
    have renamedTags : (CaseTree.renamed (pending := .tags (replyTags h))
        (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) (next.opened (ρ.up X)).2
        (upTele (swapStack stack Θ [X]) (pairsTele atoms))).1 =
        (next.opened (ρ.up X)).1.rename
          (LetCase.LocallyNameless.Tm.up (upTele (swapStack stack Θ [X]) (pairsTele atoms)).toFun) :=
      CaseTree.renamed_term (next.opened (ρ.up X)).2 (upTele (swapStack stack Θ [X]) (pairsTele atoms))
    refine ⟨unpackAt atoms i₀ M,
      (Equiv.let₁ (.refl hE) hflat₀).trans (equiv_cast out
        (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ e _) (LetCase.LocallyNameless.Tm.rename_id _))
        (congrArg (fun hh => unpackStack stack hh (unpackAt atoms i₀ M)) holdsEq)),
      unpackAt_typed_proof atoms i₀ ((weakenStack stack (Θ.snoc X)).typed 0)
        (.let₁ (HasType.rename w hE) (HasType.rename s hU₀)), ?_⟩
    refine ((unpackAt_rename (Φ := Φ) atoms (swapStack stack Θ [X]) i₀ M).trans
      (congrArg (fun i => unpackAt atoms i (M.rename
        (upTele (swapStack stack Θ [X]) (pairsTele atoms)).toFun)) idx)).trans
      (congrArg (unpackAt atoms (0 : Fin (stackSize k stack + 1))) ?_)
    exact congrArg₂ LetCase.LocallyNameless.Tm.let₁
      (congrArg (LetCase.LocallyNameless.Tm.op h) ((LetCase.LocallyNameless.Tm.rename_comp w.toFun
          (upTele (swapStack stack Θ [X]) (pairsTele atoms)).toFun (argTerm arg)).trans
        ((LetCase.LocallyNameless.Tm.rename_congr (fun _ => rfl) (argTerm arg)).trans
          (argTerm_rename arg (w.comp (upTele (swapStack stack Θ [X]) (pairsTele atoms)))))))
      ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename
          (LetCase.LocallyNameless.Tm.up (upTele (swapStack stack Θ [X]) (pairsTele atoms)).toFun) t) hopen₀).trans
        renamedTags.symm)
  | stack, _, h, _, Δ, holds, _, @SpelledLaterTags.split _ _ _ _ _ _ _ _ _ atoms nxt more l r left right,
      k, Θ, ρ, arg => by
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    let X : Ty α := tupleTy atoms
    let Y : Ty α := tagsTy (nxt :: more)
    let Rh : Ty α := tagsTy (replyTags h)
    let Γ := Θ.snoc Rt
    let H' := (holds.rename ρ).rename (weakenTele Θ [Rt])
    let ρ₂ := (ρ.up Rt).up X
    let E : LetCase.LocallyNameless.Tm Empty Φ (k + 1) := .op h (argTerm arg)
    have hE : HasType Φ Γ₀ Γ E Rh := (Derivation.op (f := h) (argTyping arg)).toHasType
    have hEX : HasType Φ Γ₀ (Γ.snoc X) (E.rename Fin.succ) Rh := HasType.rename (BoundCtx.Renaming.succ Γ X) hE
    -- the first arm
    obtain ⟨Ul, hflatL, hUl, hopenL⟩ := left.opened_equiv ρ₂
    have holdsL : (holds.rename (pastPair Δ Rt X)).rename ρ₂ = H'.rename (weakenTele Γ [X]) :=
      (Holds.rename_comp holds (pastPair Δ Rt X) ρ₂).trans
        ((congrArg (fun r => holds.rename r) (renaming_ext (ρ := (pastPair Δ Rt X).comp ρ₂)
          (π := (ρ.comp (weakenTele Θ [Rt])).comp (weakenTele Γ [X])) (fun _ => rfl))).trans
          ((Holds.rename_comp holds (ρ.comp (weakenTele Θ [Rt])) (weakenTele Γ [X])).symm.trans
            (congrArg (fun h => Holds.rename (weakenTele Γ [X]) h)
              (Holds.rename_comp holds ρ (weakenTele Θ [Rt])).symm)))
    let w := weakenStack (atoms :: stack) (Γ.snoc X)
    let s := swapStack (atoms :: stack) (Γ.snoc X) [Rh]
    let i₀ := (weakenStack stack (Γ.snoc X)).toFun 0
    let Ml : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1 + 1) (atoms :: stack)) :=
      .let₁ ((E.rename Fin.succ).rename w.toFun) (Ul.rename s.toFun)
    have outL := stack_out_proof (let_frame_proof (C := packedExitType L) _ hEX) (atoms :: stack)
      (BoundCtx.Renaming.id (Γ.snoc X))
      ((Holds.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ Rt X))).rename ρ₂) hUl
    have hAl : HasType Φ Γ₀ (stackCtx stack (Γ.snoc X)) (unpackAt atoms i₀ Ml) (packedExitType L) :=
      unpackAt_typed_proof atoms i₀ ((weakenStack stack (Γ.snoc X)).typed 0)
        (.let₁ (HasType.rename w hEX) (HasType.rename s hUl))
    have armL : Equiv false Γ₀ (Γ.snoc X)
        (.let₁ (E.rename Fin.succ) (l.rename (ρ₂.up Rh).toFun))
        (unpackStack stack (H'.rename (weakenTele Γ [X])) (unpackAt atoms i₀ Ml)) (packedExitType L) :=
      (Equiv.let₁ (.refl hEX) hflatL).trans (equiv_cast outL
        (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ e _) (LetCase.LocallyNameless.Tm.rename_id _))
        (congrArg (fun hh => unpackStack stack hh (unpackAt atoms i₀ Ml)) holdsL))
    -- the other arms
    obtain ⟨V, hflatR, hV, hopenR⟩ := right.opened_equiv (ρ.up Rt)
      (arg.rename (BoundCtx.Renaming.succ Γ Y))
    have holdsR : (holds.rename (BoundCtx.Renaming.succ Δ Rt)).rename (ρ.up Rt) = H' :=
      (Holds.rename_comp holds (BoundCtx.Renaming.succ Δ Rt) (ρ.up Rt)).trans
        ((congrArg (fun r => holds.rename r) (renaming_ext (ρ := (BoundCtx.Renaming.succ Δ Rt).comp (ρ.up Rt))
          (π := ρ.comp (weakenTele Θ [Rt])) (fun _ => rfl))).trans
          (Holds.rename_comp holds ρ (weakenTele Θ [Rt])).symm)
    have armR : Equiv false Γ₀ (Γ.snoc Y)
        (.let₁ (E.rename Fin.succ) (r.rename (((ρ.up Rt).up Y).up Rh).toFun))
        (unpackStack stack (H'.rename (weakenTele Γ [Y])) V) (packedExitType L) :=
      equiv_cast hflatR
        (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ (.op h e) _) (argTerm_rename arg (BoundCtx.Renaming.succ Γ Y)).symm)
        (congrArg (fun hh => unpackStack stack (Holds.rename (weakenTele Γ [Y]) hh) V) holdsR)
    -- the case on the stored reply moves in front of the request
    let lt := (l.rename (ρ₂.up Rh).toFun).rename (swapRenaming Γ X Rh).toFun
    let rt := (r.rename (((ρ.up Rt).up Y).up Rh).toFun).rename (swapRenaming Γ Y Rh).toFun
    have hlt : HasType Φ Γ₀ ((Γ.snoc Rh).snoc X) lt (packedExitType L) :=
      HasType.rename (swapRenaming Γ X Rh) (HasType.rename (ρ₂.up Rh) left.typing.toHasType)
    have hrt : HasType Φ Γ₀ ((Γ.snoc Rh).snoc Y) rt (packedExitType L) :=
      HasType.rename (swapRenaming Γ Y Rh) (HasType.rename (((ρ.up Rt).up Y).up Rh) right.typing.toHasType)
    have comm := let_case_comm_proof (Δ := Γ) (X := X) (Y := Y) (0 : Fin (k + 1)) rfl hE hlt hrt
    have eqL : (l.rename (swapRenaming (Δ.snoc Rt) X Rh).toFun).rename (((ρ.up Rt).up Rh).up X).toFun = lt :=
      (LetCase.LocallyNameless.Tm.rename_comp (swapRenaming (Δ.snoc Rt) X Rh).toFun (((ρ.up Rt).up Rh).up X).toFun l).trans
        ((congrArg (fun q : BoundCtx.Renaming _ _ => l.rename q.toFun)
          (swapRenaming_natural (ρ.up Rt) X Rh)).trans
          (LetCase.LocallyNameless.Tm.rename_comp (ρ₂.up Rh).toFun (swapRenaming Γ X Rh).toFun l).symm)
    have eqR : (r.rename (swapRenaming (Δ.snoc Rt) Y Rh).toFun).rename (((ρ.up Rt).up Rh).up Y).toFun = rt :=
      (LetCase.LocallyNameless.Tm.rename_comp (swapRenaming (Δ.snoc Rt) Y Rh).toFun (((ρ.up Rt).up Rh).up Y).toFun r).trans
        ((congrArg (fun q : BoundCtx.Renaming _ _ => r.rename q.toFun)
          (swapRenaming_natural (ρ.up Rt) Y Rh)).trans
          (LetCase.LocallyNameless.Tm.rename_comp (((ρ.up Rt).up Y).up Rh).toFun (swapRenaming Γ Y Rh).toFun r).symm)
    have start : Equiv false Γ₀ Γ
        (.let₁ E (.case (.bv 1) ((l.rename (swapRenaming (Δ.snoc Rt) X Rh).toFun).rename
            (((ρ.up Rt).up Rh).up X).toFun)
          ((r.rename (swapRenaming (Δ.snoc Rt) Y Rh).toFun).rename (((ρ.up Rt).up Rh).up Y).toFun)))
        (.case (.bv 0) (.let₁ (E.rename Fin.succ) (l.rename (ρ₂.up Rh).toFun))
          (.let₁ (E.rename Fin.succ) (r.rename (((ρ.up Rt).up Y).up Rh).toFun))) (packedExitType L) :=
      equiv_cast comm
        (congrArg₂ (fun x y => LetCase.LocallyNameless.Tm.let₁ E (.case (.bv 1) x y)) eqL.symm eqR.symm)
        (congrArg₂ (fun x y => LetCase.LocallyNameless.Tm.case (.bv 0) (.let₁ (E.rename Fin.succ) x) (.let₁ (E.rename Fin.succ) y))
          (swap_swap_rename Γ X Rh _) (swap_swap_rename Γ Y Rh _))
    -- the unpackings of the stack move out of both arms
    have out := case_stack_out_proof (C := packedExitType L) stack (Γ := Γ) (X := X) (Y := Y) 0 rfl H' hAl hV
    have index : (swapStack stack Θ [Rt]).toFun ((weakenStack stack Γ).toFun 0) =
        (0 : Fin (stackSize k stack + 1)) :=
      congrArg (fun r : BoundCtx.Renaming Γ _ => r.toFun 0) (swapStack_weaken stack Θ [Rt])
    refine ⟨_, (start.trans (Equiv.case (.refl (.bv (ι := (0 : Fin (k + 1))))) armL armR)).trans out,
      .case (slot_typed _ ((weakenStack stack Γ).typed 0))
        (HasType.rename (swapStack stack Γ [X]) hAl) (HasType.rename (swapStack stack Γ [Y]) hV), ?_⟩
    show LetCase.LocallyNameless.Tm.case (.bv ((swapStack stack Θ [Rt]).toFun ((weakenStack stack Γ).toFun 0)))
      (LetCase.LocallyNameless.Tm.rename ((swapStack stack Θ [Rt]).up X).toFun _)
      (LetCase.LocallyNameless.Tm.rename ((swapStack stack Θ [Rt]).up Y).toFun _) = _
    refine congr (congr (congrArg (fun i => LetCase.LocallyNameless.Tm.case (.bv i)) index) ?_) ?_
    · -- the first arm of the normal form
      have idx : (swapStack stack Θ [Rt, X]).toFun i₀ = (0 : Fin (stackSize k stack + 1 + 1)) :=
        congrArg (fun r : BoundCtx.Renaming (Γ.snoc X) _ => r.toFun 0) (swapStack_weaken stack Θ [Rt, X])
      have renamedTags : (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) (Γ.snoc X)).snoc Rh) (left.opened ρ₂).2
          (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms))).1 =
          (left.opened ρ₂).1.rename
            (LetCase.LocallyNameless.Tm.up (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms)).toFun) :=
        CaseTree.renamed_term (left.opened ρ₂).2 (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms))
      refine (((LetCase.LocallyNameless.Tm.rename_comp (swapStack stack Γ [X]).toFun ((swapStack stack Θ [Rt]).up X).toFun
          (unpackAt atoms i₀ Ml)).trans
        (congrArg (fun q : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename q.toFun (unpackAt atoms i₀ Ml))
          (swapStack_cons stack Θ Rt [X]).symm)).trans
        ((unpackAt_rename (Φ := Φ) atoms (swapStack stack Θ [Rt, X]) i₀ Ml).trans
          (congrArg (fun i => unpackAt atoms i (Ml.rename
            (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms)).toFun)) idx))).trans
        (congrArg (unpackAt atoms (0 : Fin (stackSize k stack + 1 + 1))) ?_)
      exact congrArg₂ LetCase.LocallyNameless.Tm.let₁
        (congrArg (LetCase.LocallyNameless.Tm.op h)
          ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms)).toFun t)
            (LetCase.LocallyNameless.Tm.rename_comp Fin.succ w.toFun (argTerm arg))).trans
            ((LetCase.LocallyNameless.Tm.rename_comp _ (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms)).toFun
              (argTerm arg)).trans
              ((LetCase.LocallyNameless.Tm.rename_congr (fun _ => rfl) (argTerm arg)).trans
                (argTerm_rename arg (((BoundCtx.Renaming.succ Γ X).comp w).comp
                  (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms))))))))
        ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename
            (LetCase.LocallyNameless.Tm.up (upTele (swapStack stack Θ [Rt, X]) (pairsTele atoms)).toFun) t) hopenL).trans
          renamedTags.symm)
    · -- the other arms of the normal form
      have renamedTags : (CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          (right.opened (ρ.up Rt) (arg.rename (BoundCtx.Renaming.succ Γ Y))).2 (swapStack stack Θ [Rt])).1 =
          (right.opened (ρ.up Rt) (arg.rename (BoundCtx.Renaming.succ Γ Y))).1.rename
            (LetCase.LocallyNameless.Tm.up (swapStack stack Θ [Rt]).toFun) :=
        CaseTree.renamed_term (right.opened (ρ.up Rt) (arg.rename (BoundCtx.Renaming.succ Γ Y))).2
          (swapStack stack Θ [Rt])
      exact (congrArg (fun t => LetCase.LocallyNameless.Tm.rename ((swapStack stack Θ [Rt]).up Y).toFun t) hopenR).trans
        renamedTags.symm

end

end Spelled

/-! ## Normal forms commute with renaming

The normal form of a spelled tree along a composite renaming is the
normal form along the first renaming, renamed along the second. For a
chain with a held tuple this uses the two commutations of renaming with
binding under a pending tuple. -/

section Natural

variable [TaggedSignature α Φ]

/-- Naturality of the normal form at a case on a bound reply, from the
naturality of its arms. -/
theorem split_opened_renamed {stack : List (List α)} {atoms nxt : List α} {more : List (List α)} {n : Nat}
    {Δ : BoundCtx (Ty α) n} {holds : Holds Δ stack} {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
    (left : SpelledStack (atoms :: stack) ((Δ.snoc (tagsTy (atoms :: nxt :: more))).snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: nxt :: more)) (tupleTy atoms)))) L l)
    (right : SpelledStackTags stack (nxt :: more) (Δ.snoc (tagsTy (atoms :: nxt :: more)))
      (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: nxt :: more)))) L r)
    {m : Nat} {Θ : BoundCtx (Ty α) m} {k : Nat} {δ : BoundCtx (Ty α) k} (σ : BoundCtx.Renaming Δ Θ)
    (π : BoundCtx.Renaming Θ δ)
    (ihl₀ : CaseTree.renamed (pending := .body) (left.opened ((σ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))).2
        (upStack (atoms :: stack) ((π.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))) =
      left.opened (((σ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms)).comp ((π.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))))
    (ihr₀ : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (stackCtx stack (Θ.snoc (tagsTy (atoms :: nxt :: more)))).snoc (tagsTy (nxt :: more)))
        (right.opened (σ.up (tagsTy (atoms :: nxt :: more)))).2 (upStack stack (π.up (tagsTy (atoms :: nxt :: more)))) =
      right.opened ((σ.up (tagsTy (atoms :: nxt :: more))).comp (π.up (tagsTy (atoms :: nxt :: more))))) :
    CaseTree.renamed (pending := .tags (atoms :: nxt :: more))
      (β := (stackCtx stack Θ).snoc (tagsTy (atoms :: nxt :: more)))
      ((SpelledStackTags.split atoms nxt more left right).opened σ).2 (upStack stack π) =
      (SpelledStackTags.split atoms nxt more left right).opened (σ.comp π) := by
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    let X : Ty α := tupleTy atoms
    let Y : Ty α := tagsTy (nxt :: more)
    let P := pairsTele atoms
    let σ₂ := (σ.up Rt).up X
    let π₂ := (π.up Rt).up X
    -- the first arm
    have ihl := ihl₀.trans (congrArg (fun r => left.opened r)
      ((renaming_up_comp (σ.up Rt) (π.up Rt) X).trans
        (congrArg (fun r : BoundCtx.Renaming _ _ => r.up X) (renaming_up_comp σ π Rt))))
    have el : (upTele (swapStack stack Θ [Rt, X]) P).comp
        (upTele ((upStack stack π).up Rt) (unpackTele atoms)) =
        (upStack (atoms :: stack) π₂).comp (upTele (swapStack stack δ [Rt, X]) P) :=
      (upTele_comp P (swapStack stack Θ [Rt, X]) (upTele (upStack stack π) [Rt, X])).trans
        ((congrArg (fun r => upTele r P) (swapStack_natural stack [Rt, X] π)).trans
          (upTele_comp P (upStack stack π₂) (swapStack stack δ [Rt, X])).symm)
    have stepl : CaseTree.renamed (pending := .body)
        (CaseTree.renamed (pending := .body) (left.opened σ₂).2 (upTele (swapStack stack Θ [Rt, X]) P)).2
        (upTele ((upStack stack π).up Rt) (unpackTele atoms)) =
        CaseTree.renamed (pending := .body) (left.opened (((σ.comp π).up Rt).up X)).2
          (upTele (swapStack stack δ [Rt, X]) P) :=
      (CaseTree.renamed_body_comp (left.opened σ₂).2 (upTele (swapStack stack Θ [Rt, X]) P)
          (upTele ((upStack stack π).up Rt) (unpackTele atoms))).trans
        ((congrArg (fun r => CaseTree.renamed (pending := .body) (left.opened σ₂).2 r) el).trans
          ((CaseTree.renamed_body_comp (left.opened σ₂).2 (upStack (atoms :: stack) π₂)
              (upTele (swapStack stack δ [Rt, X]) P)).symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
              CaseTree.renamed (pending := .body) r.2 (upTele (swapStack stack δ [Rt, X]) P)) ihl)))
    have armL := (CaseTree.packed_renamed atoms
        (CaseTree.renamed (pending := .body) (left.opened σ₂).2 (upTele (swapStack stack Θ [Rt, X]) P)).2
        ((upStack stack π).up Rt)).trans
      (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
          (extendCtx ((stackCtx stack δ).snoc Rt) (unpackTele atoms)) L u =>
        (⟨_, CaseTree.packed atoms r.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
          (((stackCtx stack δ).snoc Rt).snoc X) L u)) stepl)
    -- the other arms
    have ihr := ihr₀.trans
      (congrArg (fun r => right.opened r) (renaming_up_comp σ π Rt))
    have comp₁ : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := ((stackCtx stack Θ).snoc Rt).snoc Y)
        (CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          (right.opened (σ.up Rt)).2 (swapStack stack Θ [Rt])).2
        ((upStack stack π).up Rt) =
        CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          (right.opened (σ.up Rt)).2 ((swapStack stack Θ [Rt]).comp ((upStack stack π).up Rt)) :=
      CaseTree.renamed_comp (right.opened (σ.up Rt)).2 _ _
    have comp₂ : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (stackCtx stack (δ.snoc Rt)).snoc Y)
        (CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          (right.opened (σ.up Rt)).2 (upStack stack (π.up Rt))).2
        (swapStack stack δ [Rt]) =
        CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          (right.opened (σ.up Rt)).2 ((upStack stack (π.up Rt)).comp (swapStack stack δ [Rt])) :=
      CaseTree.renamed_comp (right.opened (σ.up Rt)).2 _ _
    have stepr : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := ((stackCtx stack Θ).snoc Rt).snoc Y)
        (CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          (right.opened (σ.up Rt)).2 (swapStack stack Θ [Rt])).2
        ((upStack stack π).up Rt) =
        CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (δ.snoc Rt)).snoc Y)
          (right.opened ((σ.comp π).up Rt)).2 (swapStack stack δ [Rt]) :=
      comp₁.trans
        ((congrArg (fun r => CaseTree.renamed (pending := .tags (nxt :: more))
            (β := (stackCtx stack (Θ.snoc Rt)).snoc Y) (right.opened (σ.up Rt)).2 r)
          (swapStack_natural stack [Rt] π)).trans
          (comp₂.symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (nxt :: more)) _ L u =>
              CaseTree.renamed (pending := .tags (nxt :: more))
                (β := (stackCtx stack (δ.snoc Rt)).snoc Y) r.2 (swapStack stack δ [Rt])) ihr)))
    exact congrArg₂ (fun (x : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
          (((stackCtx stack δ).snoc Rt).snoc X) L u)
        (y : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (nxt :: more))
          (((stackCtx stack δ).snoc Rt).snoc Y) L u) =>
        (⟨_, CaseTree.split atoms nxt more x.2 y.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree (.tags (atoms :: nxt :: more)) ((stackCtx stack δ).snoc Rt) L u))
      armL stepr

mutual

theorem Spelled.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : Spelled β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .body) (d.normal ρ).2 π = d.normal (ρ.comp π)
  | _, _, _, .ret exit payload, _, _, _, _, ρ, π => by
    simp only [Spelled.normal, CaseTree.renamed]
    rw [assembly_rename_comp]
  | _, _, _, .ask f argument head, _, _, _, _, ρ, π => by
    have h := head.normal_renamed ρ π
    simp only [Spelled.normal, CaseTree.renamed]
    rw [assembly_rename_comp, h]
  | _, _, _, .chain c, _, _, _, _, ρ, π => c.opened_renamed ρ π

theorem SpelledHead.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledHead tags e β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .tags tags) (β := γ.snoc (tagsTy tags)) (d.normal ρ).2 π =
      d.normal (ρ.comp π)
  | _, _, _, _, _, .bind reply, _, _, _, _, ρ, π => reply.normal_renamed ρ π
  | _, _, _, _, _, .destruct a b rest later, _, γ, _, δ, ρ, π => by
    have h := later.normal_renamed (armRenaming ρ (tupleTy (a :: b :: rest)) (.base a)) ((π.up _).up _)
    have e : (armRenaming ρ (tupleTy (a :: b :: rest)) (.base a)).comp ((π.up _).up _) =
        armRenaming (ρ.comp π) (tupleTy (a :: b :: rest)) (.base a) :=
      renaming_ext (Fin.cases rfl (fun _ => rfl))
    rw [e] at h
    simp only [SpelledHead.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, _, .branch atoms next rest left right, _, γ, _, δ, ρ, π => by
    have hl := left.normal_renamed (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))) (π.up _)
    have hr := right.normal_renamed (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))) (π.up _)
    have e : (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))).comp (π.up _) =
        (ρ.comp π).comp (BoundCtx.Renaming.succ δ (tagsTy (atoms :: next :: rest))) :=
      renaming_ext (fun _ => rfl)
    rw [e] at hl hr
    simp only [SpelledHead.normal, CaseTree.renamed]
    rw [hl, hr]

theorem SpelledTags.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTags tags β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .tags tags) (β := γ.snoc (tagsTy tags)) (d.normal ρ).2 π =
      d.normal (ρ.comp π)
  | _, _, _, _, .only atoms payload, _, _, _, _, ρ, π => by
    have h := payload.normal_renamed ρ π
    simp only [SpelledTags.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .split atoms next rest left right, _, _, _, _, ρ, π => by
    have hl := left.normal_renamed (ρ.up _) (π.up _)
    have hr := right.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at hl hr
    simp only [SpelledTags.normal, CaseTree.renamed]
    rw [hl, hr]

theorem SpelledTuple.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .tuple atoms) (β := γ.snoc (tupleTy atoms)) (d.normal ρ).2 π =
      d.normal (ρ.comp π)
  | _, _, _, _, .unit body, _, _, _, _, ρ, π => by
    have h := body.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .atom a body, _, _, _, _, ρ, π => by
    have h := body.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .pair a b rest later, _, _, _, _, ρ, π => by
    have h := later.normal_renamed ((ρ.up _).up _) ((π.up _).up _)
    rw [renaming_up_comp, renaming_up_comp] at h
    simp only [SpelledTuple.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .hold atoms chain, _, _, _, δ, ρ, π => by
    have h := (chain.opened_renamed (ρ.up (tupleTy atoms)) (π.up (tupleTy atoms))).trans
      (congrArg (fun r => chain.opened r) (renaming_up_comp ρ π (tupleTy atoms)))
    exact (CaseTree.packed_renamed atoms (chain.opened (ρ.up (tupleTy atoms))).2 π).trans
      (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body (extendCtx δ (unpackTele atoms)) L u =>
        (⟨_, CaseTree.packed atoms r.2⟩ :
          (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms) (δ.snoc (tupleTy atoms)) L u)) h)

/-- The body of the normal form of a chain over a stack commutes with
renaming. The slots of the unpackings of the stack stay in place. -/
theorem SpelledStack.opened_renamed : {stack : List (List α)} → {n : Nat} → {Δ : BoundCtx (Ty α) n} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledStack stack Δ holds L t) → {m : Nat} →
    {Θ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) →
    (π : BoundCtx.Renaming Θ δ) →
    CaseTree.renamed (pending := .body) (d.opened σ).2 (upStack stack π) = d.opened (σ.comp π)
  | _, _, _, _, _, .done body, _, _, _, _, σ, π => body.normal_renamed σ π
  | _, _, _, _, _, .unit next, _, _, _, _, σ, π => next.opened_renamed σ π
  | _, _, _, _, _, .atom next, _, _, _, _, σ, π => next.opened_renamed σ π
  | (a :: b :: rest) :: stack, _, _, _, _, .step next, _, Θ, _, δ, σ, π => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    let P := pairsTele (b :: rest)
    let σ₂ := (σ.up A).up T
    let π₂ := (π.up A).up T
    have ih := (next.opened_renamed σ₂ π₂).trans (congrArg (fun r => next.opened r)
      ((renaming_up_comp (σ.up A) (π.up A) T).trans
        (congrArg (fun r : BoundCtx.Renaming _ _ => r.up T) (renaming_up_comp σ π A))))
    have e : (upTele (swapStack stack Θ [A, T]) P).comp (upStack ((a :: b :: rest) :: stack) π) =
        (upStack ((b :: rest) :: stack) π₂).comp (upTele (swapStack stack δ [A, T]) P) :=
      (upTele_comp P (swapStack stack Θ [A, T]) (upTele (upStack stack π) [A, T])).trans
        ((congrArg (fun r => upTele r P) (swapStack_natural stack [A, T] π)).trans
          (upTele_comp P (upStack stack π₂) (swapStack stack δ [A, T])).symm)
    exact (CaseTree.renamed_body_comp (next.opened σ₂).2 (upTele (swapStack stack Θ [A, T]) P)
        (upStack ((a :: b :: rest) :: stack) π)).trans
      ((congrArg (fun r => CaseTree.renamed (pending := .body) (next.opened σ₂).2 r) e).trans
        ((CaseTree.renamed_body_comp (next.opened σ₂).2 (upStack ((b :: rest) :: stack) π₂)
            (upTele (swapStack stack δ [A, T]) P)).symm.trans
          (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
            CaseTree.renamed (pending := .body) r.2 (upTele (swapStack stack δ [A, T]) P)) ih)))
  | stack, _, _, _, _, .ask g argument reply, _, Θ, _, δ, σ, π => by
    have h := reply.opened_renamed σ π
    have e : (σ.comp (weakenStack stack Θ)).comp (upStack stack π) = (σ.comp π).comp (weakenStack stack δ) :=
      congrArg (fun r => σ.comp r) (weakenStack_natural stack π)
    simp only [SpelledStack.opened, CaseTree.renamed]
    rw [assembly_rename_comp, e, h]

  | stack, _, _, _, _, .pick sel next, _, Θ, _, δ, σ, π =>
    (CaseTree.renamed_body_comp (next.opened σ).2 (selectRen sel Θ) (upStack stack π)).trans
      ((congrArg (fun r => CaseTree.renamed (pending := .body) (next.opened σ).2 r)
        (selectRen_natural sel π)).trans
        ((CaseTree.renamed_body_comp (next.opened σ).2 (upStack (_ :: _) π) (selectRen sel δ)).symm.trans
          (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
            CaseTree.renamed (pending := .body) r.2 (selectRen sel δ)) (next.opened_renamed σ π))))

/-- The normal form of the bound reply of a request of such a chain
commutes with renaming. -/
theorem SpelledStackTags.opened_renamed : {stack : List (List α)} → {tags : List (List α)} → {n : Nat} →
    {Δ : BoundCtx (Ty α) n} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} →
    (d : SpelledStackTags stack tags Δ holds L t) → {m : Nat} → {Θ : BoundCtx (Ty α) m} → {k : Nat} →
    {δ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) → (π : BoundCtx.Renaming Θ δ) →
    CaseTree.renamed (pending := .tags tags) (β := (stackCtx stack Θ).snoc (tagsTy tags))
      (d.opened σ).2 (upStack stack π) = d.opened (σ.comp π)
  | stack, _, _, _, _, _, .bind atoms next, _, Θ, _, δ, σ, π => by
    let X : Ty α := tupleTy atoms
    let P := pairsTele atoms
    have ih := (next.opened_renamed (σ.up X) (π.up X)).trans
      (congrArg (fun r => next.opened r) (renaming_up_comp σ π X))
    have e : (upTele (swapStack stack Θ [X]) P).comp (upTele (upStack stack π) (unpackTele atoms)) =
        (upStack (atoms :: stack) (π.up X)).comp (upTele (swapStack stack δ [X]) P) :=
      (upTele_comp P (swapStack stack Θ [X]) (upTele (upStack stack π) [X])).trans
        ((congrArg (fun r => upTele r P) (swapStack_natural stack [X] π)).trans
          (upTele_comp P (upStack stack (π.up X)) (swapStack stack δ [X])).symm)
    have step : CaseTree.renamed (pending := .body)
        (CaseTree.renamed (pending := .body) (next.opened (σ.up X)).2 (upTele (swapStack stack Θ [X]) P)).2
        (upTele (upStack stack π) (unpackTele atoms)) =
        CaseTree.renamed (pending := .body) (next.opened ((σ.comp π).up X)).2
          (upTele (swapStack stack δ [X]) P) :=
      (CaseTree.renamed_body_comp (next.opened (σ.up X)).2 (upTele (swapStack stack Θ [X]) P)
          (upTele (upStack stack π) (unpackTele atoms))).trans
        ((congrArg (fun r => CaseTree.renamed (pending := .body) (next.opened (σ.up X)).2 r) e).trans
          ((CaseTree.renamed_body_comp (next.opened (σ.up X)).2 (upStack (atoms :: stack) (π.up X))
              (upTele (swapStack stack δ [X]) P)).symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
              CaseTree.renamed (pending := .body) r.2 (upTele (swapStack stack δ [X]) P)) ih)))
    exact congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms) ((stackCtx stack δ).snoc X) L u =>
        (⟨_, CaseTree.only atoms q.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree (.tags [atoms]) ((stackCtx stack δ).snoc X) L u))
      ((CaseTree.packed_renamed atoms
          (CaseTree.renamed (pending := .body) (next.opened (σ.up X)).2 (upTele (swapStack stack Θ [X]) P)).2
          (upStack stack π)).trans
        (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
            (extendCtx (stackCtx stack δ) (unpackTele atoms)) L u =>
          (⟨_, CaseTree.packed atoms r.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
            CaseTree (.tuple atoms) ((stackCtx stack δ).snoc X) L u)) step))
  | _, _, _, _, _, _, .split _ _ _ left right, _, _, _, _, σ, π =>
    split_opened_renamed left right σ π (left.opened_renamed _ _) (right.opened_renamed _ _)
  | _, _, _, _, _, _, .deferred _ _ _ _ left right _ _, _, _, _, _, σ, π =>
    split_opened_renamed left right σ π (left.opened_renamed _ _) (right.opened_renamed _ _)
  | _, tags, _, _, _, _, .later _ argument arms, _, _, _, _, σ, π =>
    (arms.opened_renamed σ π (argument.rename (σ.up (tagsTy tags)))).trans
      (congrArg (fun a => arms.opened (σ.comp π) a)
        ((assembly_rename_comp argument (σ.up (tagsTy tags)) (π.up (tagsTy tags))).trans
          (congrArg (fun q => argument.rename q) (renaming_up_comp σ π (tagsTy tags)))))

/-- The normal form of a reply inspected after one later request commutes
with renaming. The request is renamed with the base context. -/
theorem SpelledLaterTags.opened_renamed : {stack : List (List α)} → {tags : List (List α)} → {h : Φ} →
    {n : Nat} → {Δ : BoundCtx (Ty α) n} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)} →
    (d : SpelledLaterTags stack tags h Δ holds L t) → {m : Nat} → {Θ : BoundCtx (Ty α) m} → {k : Nat} →
    {δ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) → (π : BoundCtx.Renaming Θ δ) →
    (arg : Assembly (Θ.snoc (tagsTy tags)) (instrSrc h)) →
    CaseTree.renamed (pending := .tags tags) (β := (stackCtx stack Θ).snoc (tagsTy tags))
      (d.opened σ arg).2 (upStack stack π) = d.opened (σ.comp π) (arg.rename (π.up (tagsTy tags)))
  | stack, _, h, _, _, _, _, .only atoms next, _, Θ, _, δ, σ, π, arg => by
    let X : Ty α := tupleTy atoms
    let Rh : Ty α := tagsTy (replyTags h)
    let P := pairsTele atoms
    let N := next.opened (σ.up X)
    have ih := (next.opened_renamed (σ.up X) (π.up X)).trans
      (congrArg (fun q => next.opened q) (renaming_up_comp σ π X))
    have e : (upTele (swapStack stack Θ [X]) P).comp (upTele (upStack stack π) (unpackTele atoms)) =
        (upStack (atoms :: stack) (π.up X)).comp (upTele (swapStack stack δ [X]) P) :=
      (upTele_comp P (swapStack stack Θ [X]) (upTele (upStack stack π) [X])).trans
        ((congrArg (fun q => upTele q P) (swapStack_natural stack [X] π)).trans
          (upTele_comp P (upStack stack (π.up X)) (swapStack stack δ [X])).symm)
    have aEq : (arg.rename ((weakenStack (atoms :: stack) (Θ.snoc X)).comp
          (upTele (swapStack stack Θ [X]) P))).rename (upTele (upStack stack π) (unpackTele atoms)) =
        (arg.rename (π.up X)).rename ((weakenStack (atoms :: stack) (δ.snoc X)).comp
          (upTele (swapStack stack δ [X]) P)) :=
      (assembly_rename_comp arg _ _).trans
        ((congrArg (fun q => arg.rename q)
          ((congrArg (fun q => (weakenStack (atoms :: stack) (Θ.snoc X)).comp q) e).trans
            (congrArg (fun q => BoundCtx.Renaming.comp q (upTele (swapStack stack δ [X]) P))
              (weakenStack_natural (atoms :: stack) (π.up X))))).trans
          (assembly_rename_comp arg (π.up X) ((weakenStack (atoms :: stack) (δ.snoc X)).comp
            (upTele (swapStack stack δ [X]) P))).symm)
    have comp₁ : CaseTree.renamed (pending := .tags (replyTags h))
        (β := (extendCtx (stackCtx stack Θ) (unpackTele atoms)).snoc Rh)
        (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) N.2 (upTele (swapStack stack Θ [X]) P)).2
        (upTele (upStack stack π) (unpackTele atoms)) =
        CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) N.2
          ((upTele (swapStack stack Θ [X]) P).comp (upTele (upStack stack π) (unpackTele atoms))) :=
      CaseTree.renamed_comp N.2 _ _
    have comp₂ : CaseTree.renamed (pending := .tags (replyTags h))
        (β := (stackCtx (atoms :: stack) (δ.snoc X)).snoc Rh)
        (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) N.2 (upStack (atoms :: stack) (π.up X))).2
        (upTele (swapStack stack δ [X]) P) =
        CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) N.2
          ((upStack (atoms :: stack) (π.up X)).comp (upTele (swapStack stack δ [X]) P)) :=
      CaseTree.renamed_comp N.2 _ _
    have rEq : CaseTree.renamed (pending := .tags (replyTags h))
        (β := (extendCtx (stackCtx stack Θ) (unpackTele atoms)).snoc Rh)
        (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) N.2 (upTele (swapStack stack Θ [X]) P)).2
        (upTele (upStack stack π) (unpackTele atoms)) =
        CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) (δ.snoc X)).snoc Rh)
          (next.opened ((σ.comp π).up X)).2 (upTele (swapStack stack δ [X]) P) :=
      comp₁.trans
        ((congrArg (fun q => CaseTree.renamed (pending := .tags (replyTags h))
            (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) N.2 q) e).trans
          (comp₂.symm.trans
            (congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (replyTags h)) _ L u =>
              CaseTree.renamed (pending := .tags (replyTags h))
                (β := (stackCtx (atoms :: stack) (δ.snoc X)).snoc Rh) q.2
                (upTele (swapStack stack δ [X]) P)) ih)))
    let B := CaseTree.ask h
      (arg.rename ((weakenStack (atoms :: stack) (Θ.snoc X)).comp (upTele (swapStack stack Θ [X]) P)))
      (CaseTree.renamed (pending := .tags (replyTags h))
        (β := (stackCtx (atoms :: stack) (Θ.snoc X)).snoc Rh) N.2 (upTele (swapStack stack Θ [X]) P)).2
    have body : CaseTree.renamed (pending := .body) B (upTele (upStack stack π) (unpackTele atoms)) =
        ⟨_, CaseTree.ask h
          ((arg.rename (π.up X)).rename ((weakenStack (atoms :: stack) (δ.snoc X)).comp
            (upTele (swapStack stack δ [X]) P)))
          (CaseTree.renamed (pending := .tags (replyTags h))
            (β := (stackCtx (atoms :: stack) (δ.snoc X)).snoc Rh)
            (next.opened ((σ.comp π).up X)).2 (upTele (swapStack stack δ [X]) P)).2⟩ :=
      congrArg₂ (fun (x : Assembly (extendCtx (stackCtx stack δ) (unpackTele atoms)) (instrSrc h))
        (y : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (replyTags h))
          ((extendCtx (stackCtx stack δ) (unpackTele atoms)).snoc Rh) L u) =>
        (⟨_, CaseTree.ask h x y.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree .body (extendCtx (stackCtx stack δ) (unpackTele atoms)) L u)) aEq rEq
    exact congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms) ((stackCtx stack δ).snoc X) L u =>
        (⟨_, CaseTree.only atoms q.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree (.tags [atoms]) ((stackCtx stack δ).snoc X) L u))
      ((CaseTree.packed_renamed atoms B (upStack stack π)).trans
        (congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
            (extendCtx (stackCtx stack δ) (unpackTele atoms)) L u =>
          (⟨_, CaseTree.packed atoms q.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
            CaseTree (.tuple atoms) ((stackCtx stack δ).snoc X) L u)) body))
  | stack, _, h, _, _, _, _, .split atoms nxt more left right, _, Θ, _, δ, σ, π, arg => by
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    let X : Ty α := tupleTy atoms
    let Y : Ty α := tagsTy (nxt :: more)
    let Rh : Ty α := tagsTy (replyTags h)
    let P := pairsTele atoms
    let σ₂ := (σ.up Rt).up X
    let π₂ := (π.up Rt).up X
    let N := left.opened σ₂
    -- the first arm
    have ihl := (left.opened_renamed σ₂ π₂).trans (congrArg (fun q => left.opened q)
      ((renaming_up_comp (σ.up Rt) (π.up Rt) X).trans
        (congrArg (fun q : BoundCtx.Renaming _ _ => q.up X) (renaming_up_comp σ π Rt))))
    have el : (upTele (swapStack stack Θ [Rt, X]) P).comp
        (upTele ((upStack stack π).up Rt) (unpackTele atoms)) =
        (upStack (atoms :: stack) π₂).comp (upTele (swapStack stack δ [Rt, X]) P) :=
      (upTele_comp P (swapStack stack Θ [Rt, X]) (upTele (upStack stack π) [Rt, X])).trans
        ((congrArg (fun q => upTele q P) (swapStack_natural stack [Rt, X] π)).trans
          (upTele_comp P (upStack stack π₂) (swapStack stack δ [Rt, X])).symm)
    have aEq : (arg.rename (((BoundCtx.Renaming.succ (Θ.snoc Rt) X).comp
          (weakenStack (atoms :: stack) ((Θ.snoc Rt).snoc X))).comp
          (upTele (swapStack stack Θ [Rt, X]) P))).rename
          (upTele ((upStack stack π).up Rt) (unpackTele atoms)) =
        (arg.rename (π.up Rt)).rename (((BoundCtx.Renaming.succ (δ.snoc Rt) X).comp
          (weakenStack (atoms :: stack) ((δ.snoc Rt).snoc X))).comp
          (upTele (swapStack stack δ [Rt, X]) P)) :=
      (assembly_rename_comp arg _ _).trans
        ((congrArg (fun q => arg.rename q)
          ((congrArg (fun q => ((BoundCtx.Renaming.succ (Θ.snoc Rt) X).comp
              (weakenStack (atoms :: stack) ((Θ.snoc Rt).snoc X))).comp q) el).trans
            ((congrArg (fun q => (BoundCtx.Renaming.succ (Θ.snoc Rt) X).comp
                (BoundCtx.Renaming.comp q (upTele (swapStack stack δ [Rt, X]) P)))
              (weakenStack_natural (atoms :: stack) π₂)).trans
              (congrArg (fun q => BoundCtx.Renaming.comp q
                  ((weakenStack (atoms :: stack) ((δ.snoc Rt).snoc X)).comp
                    (upTele (swapStack stack δ [Rt, X]) P)))
                (renaming_ext (ρ := (BoundCtx.Renaming.succ (Θ.snoc Rt) X).comp π₂)
                  (π := (π.up Rt).comp (BoundCtx.Renaming.succ (δ.snoc Rt) X)) (fun _ => rfl)))))).trans
          (assembly_rename_comp arg (π.up Rt) (((BoundCtx.Renaming.succ (δ.snoc Rt) X).comp
            (weakenStack (atoms :: stack) ((δ.snoc Rt).snoc X))).comp
            (upTele (swapStack stack δ [Rt, X]) P))).symm)
    have comp₁ : CaseTree.renamed (pending := .tags (replyTags h))
        (β := (extendCtx ((stackCtx stack Θ).snoc Rt) (unpackTele atoms)).snoc Rh)
        (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) ((Θ.snoc Rt).snoc X)).snoc Rh) N.2
          (upTele (swapStack stack Θ [Rt, X]) P)).2
        (upTele ((upStack stack π).up Rt) (unpackTele atoms)) =
        CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) ((Θ.snoc Rt).snoc X)).snoc Rh) N.2
          ((upTele (swapStack stack Θ [Rt, X]) P).comp
            (upTele ((upStack stack π).up Rt) (unpackTele atoms))) :=
      CaseTree.renamed_comp N.2 _ _
    have comp₂ : CaseTree.renamed (pending := .tags (replyTags h))
        (β := (stackCtx (atoms :: stack) ((δ.snoc Rt).snoc X)).snoc Rh)
        (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) ((Θ.snoc Rt).snoc X)).snoc Rh) N.2
          (upStack (atoms :: stack) π₂)).2
        (upTele (swapStack stack δ [Rt, X]) P) =
        CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) ((Θ.snoc Rt).snoc X)).snoc Rh) N.2
          ((upStack (atoms :: stack) π₂).comp (upTele (swapStack stack δ [Rt, X]) P)) :=
      CaseTree.renamed_comp N.2 _ _
    have rEq : CaseTree.renamed (pending := .tags (replyTags h))
        (β := (extendCtx ((stackCtx stack Θ).snoc Rt) (unpackTele atoms)).snoc Rh)
        (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) ((Θ.snoc Rt).snoc X)).snoc Rh) N.2
          (upTele (swapStack stack Θ [Rt, X]) P)).2
        (upTele ((upStack stack π).up Rt) (unpackTele atoms)) =
        CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) ((δ.snoc Rt).snoc X)).snoc Rh)
          (left.opened (((σ.comp π).up Rt).up X)).2 (upTele (swapStack stack δ [Rt, X]) P) :=
      comp₁.trans
        ((congrArg (fun q => CaseTree.renamed (pending := .tags (replyTags h))
            (β := (stackCtx (atoms :: stack) ((Θ.snoc Rt).snoc X)).snoc Rh) N.2 q) el).trans
          (comp₂.symm.trans
            (congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (replyTags h)) _ L u =>
              CaseTree.renamed (pending := .tags (replyTags h))
                (β := (stackCtx (atoms :: stack) ((δ.snoc Rt).snoc X)).snoc Rh) q.2
                (upTele (swapStack stack δ [Rt, X]) P)) ihl)))
    let B := CaseTree.ask h
      (arg.rename (((BoundCtx.Renaming.succ (Θ.snoc Rt) X).comp
        (weakenStack (atoms :: stack) ((Θ.snoc Rt).snoc X))).comp (upTele (swapStack stack Θ [Rt, X]) P)))
      (CaseTree.renamed (pending := .tags (replyTags h))
        (β := (stackCtx (atoms :: stack) ((Θ.snoc Rt).snoc X)).snoc Rh) N.2
        (upTele (swapStack stack Θ [Rt, X]) P)).2
    have body : CaseTree.renamed (pending := .body) B
        (upTele ((upStack stack π).up Rt) (unpackTele atoms)) =
        ⟨_, CaseTree.ask h
          ((arg.rename (π.up Rt)).rename (((BoundCtx.Renaming.succ (δ.snoc Rt) X).comp
            (weakenStack (atoms :: stack) ((δ.snoc Rt).snoc X))).comp
            (upTele (swapStack stack δ [Rt, X]) P)))
          (CaseTree.renamed (pending := .tags (replyTags h))
            (β := (stackCtx (atoms :: stack) ((δ.snoc Rt).snoc X)).snoc Rh)
            (left.opened (((σ.comp π).up Rt).up X)).2 (upTele (swapStack stack δ [Rt, X]) P)).2⟩ :=
      congrArg₂ (fun (x : Assembly (extendCtx ((stackCtx stack δ).snoc Rt) (unpackTele atoms))
          (instrSrc h))
        (y : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (replyTags h))
          ((extendCtx ((stackCtx stack δ).snoc Rt) (unpackTele atoms)).snoc Rh) L u) =>
        (⟨_, CaseTree.ask h x y.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree .body (extendCtx ((stackCtx stack δ).snoc Rt) (unpackTele atoms)) L u)) aEq rEq
    have armL := (CaseTree.packed_renamed atoms B ((upStack stack π).up Rt)).trans
      (congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
          (extendCtx ((stackCtx stack δ).snoc Rt) (unpackTele atoms)) L u =>
        (⟨_, CaseTree.packed atoms q.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
          (((stackCtx stack δ).snoc Rt).snoc X) L u)) body)
    -- the other arms
    let V := right.opened (σ.up Rt) (arg.rename (BoundCtx.Renaming.succ (Θ.snoc Rt) Y))
    have argEq : (arg.rename (BoundCtx.Renaming.succ (Θ.snoc Rt) Y)).rename ((π.up Rt).up Y) =
        (arg.rename (π.up Rt)).rename (BoundCtx.Renaming.succ (δ.snoc Rt) Y) :=
      (assembly_rename_comp arg _ _).trans
        ((congrArg (fun q => arg.rename q)
          (renaming_ext (ρ := (BoundCtx.Renaming.succ (Θ.snoc Rt) Y).comp ((π.up Rt).up Y))
            (π := (π.up Rt).comp (BoundCtx.Renaming.succ (δ.snoc Rt) Y)) (fun _ => rfl))).trans
          (assembly_rename_comp arg (π.up Rt) _).symm)
    have ihr := (right.opened_renamed (σ.up Rt) (π.up Rt)
        (arg.rename (BoundCtx.Renaming.succ (Θ.snoc Rt) Y))).trans
      (congrArg₂ (fun q a => right.opened q a) (renaming_up_comp σ π Rt) argEq)
    have compR₁ : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := ((stackCtx stack Θ).snoc Rt).snoc Y)
        (CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          V.2 (swapStack stack Θ [Rt])).2
        ((upStack stack π).up Rt) =
        CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          V.2 ((swapStack stack Θ [Rt]).comp ((upStack stack π).up Rt)) :=
      CaseTree.renamed_comp V.2 _ _
    have compR₂ : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (stackCtx stack (δ.snoc Rt)).snoc Y)
        (CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          V.2 (upStack stack (π.up Rt))).2
        (swapStack stack δ [Rt]) =
        CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          V.2 ((upStack stack (π.up Rt)).comp (swapStack stack δ [Rt])) :=
      CaseTree.renamed_comp V.2 _ _
    have stepr : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := ((stackCtx stack Θ).snoc Rt).snoc Y)
        (CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (Θ.snoc Rt)).snoc Y)
          V.2 (swapStack stack Θ [Rt])).2
        ((upStack stack π).up Rt) =
        CaseTree.renamed (pending := .tags (nxt :: more)) (β := (stackCtx stack (δ.snoc Rt)).snoc Y)
          (right.opened ((σ.comp π).up Rt)
            ((arg.rename (π.up Rt)).rename (BoundCtx.Renaming.succ (δ.snoc Rt) Y))).2
          (swapStack stack δ [Rt]) :=
      compR₁.trans
        ((congrArg (fun q => CaseTree.renamed (pending := .tags (nxt :: more))
            (β := (stackCtx stack (Θ.snoc Rt)).snoc Y) V.2 q)
          (swapStack_natural stack [Rt] π)).trans
          (compR₂.symm.trans
            (congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (nxt :: more)) _ L u =>
              CaseTree.renamed (pending := .tags (nxt :: more))
                (β := (stackCtx stack (δ.snoc Rt)).snoc Y) q.2 (swapStack stack δ [Rt])) ihr)))
    exact congrArg₂ (fun (x : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
          (((stackCtx stack δ).snoc Rt).snoc X) L u)
        (y : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (nxt :: more))
          (((stackCtx stack δ).snoc Rt).snoc Y) L u) =>
        (⟨_, CaseTree.split atoms nxt more x.2 y.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree (.tags (atoms :: nxt :: more)) ((stackCtx stack δ).snoc Rt) L u))
      armL stepr

end

end Natural

section Binary

variable [BinarySignature α Φ]

/-- A direct case tree, renamed, is natively equal to its normal form. This
is the equation of its spelled tree. -/
theorem normal_equiv_proof {t : LetCase.LocallyNameless.Tm Empty Φ n} (d : DirectTree β L t) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (t.rename ρ.toFun) (d.normal ρ).1 (packedExitType L) :=
  d.spelled.normal_equiv ρ

/-! ## The normal form determines the direct tree -/

omit [BinarySignature α Φ] in
private theorem exit_term_inj {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B) {m : Nat}
    (t t' : LetCase.LocallyNameless.Tm Empty Φ m) (h : e.term t = e'.term t') :
    t = t' ∧ ∀ {k : Nat} (s : LetCase.LocallyNameless.Tm Empty Φ k), e.term s = e'.term s := by
  induction e with
  | here =>
    cases e' with
    | here => exact ⟨LetCase.LocallyNameless.Tm.inl.inj h, fun _ => rfl⟩
    | there later => cases h
  | there later ih =>
    cases e' with
    | here => cases h
    | there later' =>
      obtain ⟨terms, exits⟩ := ih later' (LetCase.LocallyNameless.Tm.inr.inj h)
      exact ⟨terms, fun s => congrArg LetCase.LocallyNameless.Tm.inr (exits s)⟩

omit [BinarySignature α Φ] in
private theorem payload_rename_inj {A B : Ty α} (p : Assembly β A) (q : Assembly β B) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) (inj : Function.Injective ρ.toFun)
    (h : argTerm (Φ := Φ) (p.rename ρ) = argTerm (q.rename ρ)) : argTerm (Φ := Φ) p = argTerm q := by
  induction p generalizing B with
  | atom s =>
    cases q with
    | atom s' => exact congrArg LetCase.LocallyNameless.Tm.bv (inj (LetCase.LocallyNameless.Tm.bv.inj h))
    | unit => cases h
    | pair x y => cases h
  | unit =>
    cases q with
    | atom s' => cases h
    | unit => rfl
    | pair x y => cases h
  | pair a b iha ihb =>
    cases q with
    | atom s' => cases h
    | unit => cases h
    | pair x y =>
      have parts := LetCase.LocallyNameless.Tm.pair.inj h
      exact congrArg₂ LetCase.LocallyNameless.Tm.pair (iha x parts.1) (ihb y parts.2)

omit [BinarySignature α Φ] in
private theorem arm_injective {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ)
    (inj : Function.Injective ρ.toFun) (reply payload : Ty α) :
    Function.Injective (armRenaming ρ reply payload).toFun := by
  intro i j
  refine Fin.cases (fun h => ?_) (fun i h => ?_) i
  · revert h
    refine Fin.cases (fun _ => rfl) (fun j h => ?_) j
    exact absurd (congrArg Fin.val h) (by simp [armRenaming, BoundCtx.Renaming.up, BoundCtx.Renaming.comp,
      BoundCtx.Renaming.succ])
  · revert h
    refine Fin.cases (fun h => ?_) (fun j h => ?_) j
    · exact absurd (congrArg Fin.val h) (by simp [armRenaming, BoundCtx.Renaming.up, BoundCtx.Renaming.comp,
        BoundCtx.Renaming.succ])
    · have inner : (ρ.toFun i).succ = (ρ.toFun j).succ := Fin.succ_injective _ h
      exact congrArg Fin.succ (inj (Fin.succ_injective _ inner))

/-- Two direct case trees with the same normal form along an injective
renaming are the same term. -/
theorem normal_injective_proof {t : LetCase.LocallyNameless.Tm Empty Φ n} (p : DirectTree β L t) :
    ∀ {u : LetCase.LocallyNameless.Tm Empty Φ n} (q : DirectTree β L u) {m : Nat}
      {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ), Function.Injective ρ.toFun →
      (p.normal ρ).1 = (q.normal ρ).1 → t = u := by
  induction p with
  | @ret _ β L A exit payload =>
    intro u q m γ ρ inj h
    cases q with
    | ret exit' payload' =>
      obtain ⟨terms, exits⟩ := exit_term_inj exit exit' _ _ h
      rw [payload_rename_inj payload payload' ρ inj terms]
      exact exits _
    | ask g b left' right' => cases exit <;> cases h
  | @ask _ β L f argument l r left right ihl ihr =>
    intro u q m γ ρ inj h
    cases q with
    | ret exit' payload' => cases exit' <;> cases h
    | ask g b left' right' =>
      have parts := LetCase.LocallyNameless.Tm.let₁.inj h
      obtain ⟨rfl, arguments⟩ := LetCase.LocallyNameless.Tm.op.inj parts.1
      have arms := LetCase.LocallyNameless.Tm.case.inj parts.2
      rw [payload_rename_inj argument b ρ inj arguments,
        ihl left' (armRenaming ρ _ _) (arm_injective ρ inj _ _) arms.2.1,
        ihr right' (armRenaming ρ _ _) (arm_injective ρ inj _ _) arms.2.2]

end Binary

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
