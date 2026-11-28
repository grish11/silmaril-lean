module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

open Region (packedExitType)
open LetCase.LocallyNameless (Equiv Pure)
open LetCase.LocallyNameless.Tm (bsubst bsubst_rename bsubst_id rename instantiate)
local notation "Term" => LetCase.LocallyNameless.Tm Empty
local notation "Typed" => LetCase.LocallyNameless.HasType

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] {pe : ε}
  {n m : Nat} {β : BoundCtx τ n} {γ : BoundCtx τ m} {L R : LCtx τ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

set_option backward.isDefEq.respectTransparency false

private def slot {A : τ} : Operand Φ (γ.snoc A) A :=
  ⟨.bv 0, .bv⟩

private theorem instantiate_lift {k a : Term Φ m} : instantiate k.lift a = k := by
  unfold instantiate LetCase.LocallyNameless.Tm.lift
  rw [bsubst_rename]
  exact bsubst_id k

private theorem empty_context {t u : Term Φ (m + 1)} {D : τ}
    (dt : Typed Φ Γ₀ (γ.snoc Silmaril.empty) t D) (du : Typed Φ Γ₀ (γ.snoc Silmaril.empty) u D) :
    Equiv pe Γ₀ (γ.snoc Silmaril.empty) t u D := by
  have impossible : Typed Φ Γ₀ (γ.snoc Silmaril.empty) (.bv 0) Silmaril.empty := .bv
  have abort : Typed Φ Γ₀ (γ.snoc Silmaril.empty) (.abort (.bv 0)) Silmaril.unit := .abort impossible
  have left := Equiv.letBeta (pureEff := pe) (.abort .bv) abort dt.lift
  have right := Equiv.letBeta (pureEff := pe) (.abort .bv) abort du.lift
  rw [instantiate_lift] at left right
  exact left.symm.trans ((Equiv.emptyInitial (A := (Silmaril.unit : τ)) impossible dt.lift du.lift).trans right)

private theorem inject_tail {A : τ} :
    {L : LCtx τ} → (q : ExitSuffix L (A :: R)) → (a : Operand Φ γ (packedExitType R)) →
    (q.tail.inject a).1 = (q.inject ⟨.inr a.1, .inr a.2⟩).1
  | _, .here, _ => rfl
  | _, .skip _ p, a => congrArg LetCase.LocallyNameless.Tm.inr (inject_tail p a)

private theorem tag_head {A : τ} :
    {L : LCtx τ} → (q : ExitSuffix L (A :: R)) → (a : Operand Φ γ A) →
    (FiniteExit.tag L q.offset (Nat.add_zero q.offset ▸ q.at (i := 0) rfl) a).1 =
      (q.inject ⟨.inl a.1, .inl a.2⟩).1
  | _, .here, _ => rfl
  | _, .skip _ p, a => congrArg LetCase.LocallyNameless.Tm.inr (tag_head p a)

private theorem instantiate_tag (q : ExitSuffix L R) (a : Operand Φ γ (packedExitType R)) :
    instantiate (q.inject (slot (γ := γ))).1 a.1 = (q.inject a).1 := by
  induction q with
  | here => rfl
  | skip _ q ih => exact congrArg LetCase.LocallyNameless.Tm.inr (ih a)

private theorem instantiate_tag_under {A : τ} (q : ExitSuffix L R)
    (a : Operand Φ (γ.snoc A) (packedExitType R)) :
    instantiate ((q.inject (slot (γ := γ))).1.underBinder) a.1 = (q.inject a).1 := by
  induction q with
  | here => rfl
  | skip _ q ih => exact congrArg LetCase.LocallyNameless.Tm.inr (ih a)

/-- The suffix injection commutes with inspecting the already bound tag.
The two substitutions use constructor values at the payload binders. -/
private theorem inject_case_eta {A : τ} (q : ExitSuffix L (A :: R)) :
    let δ := γ.snoc (packedExitType (A :: R))
    let l : Operand Φ (δ.snoc A) (packedExitType (A :: R)) := ⟨.inl (.bv 0), .inl .bv⟩
    let r : Operand Φ (δ.snoc (packedExitType R)) (packedExitType (A :: R)) := ⟨.inr (.bv 0), .inr .bv⟩
    Equiv pe Γ₀ δ (.case (.bv 0) (q.inject l).1 (q.inject r).1) (q.inject (slot (γ := γ))).1
      (packedExitType L) := by
  intro δ l r
  let k := q.inject (slot (Φ := Φ) (γ := δ))
  let scr : Typed Φ Γ₀ δ (.bv 0) (packedExitType (A :: R)) := .bv
  have bind := Equiv.bindLetCase (pureEff := pe) scr l.2.toHasType r.2.toHasType k.2.toHasType
  have left := Equiv.letBeta (pureEff := pe) (.inl .bv) l.2.toHasType k.2.toHasType.underBinder
  have right := Equiv.letBeta (pureEff := pe) (.inr .bv) r.2.toHasType k.2.toHasType.underBinder
  have finish := Equiv.letBeta (pureEff := pe) .bv scr k.2.toHasType
  change Equiv pe Γ₀ (δ.snoc A) (.let₁ l.1 k.1.underBinder) (instantiate k.1.underBinder l.1)
    (packedExitType L) at left
  change Equiv pe Γ₀ (δ.snoc (packedExitType R)) (.let₁ r.1 k.1.underBinder) (instantiate k.1.underBinder r.1)
    (packedExitType L) at right
  rw [instantiate_tag_under q l] at left
  rw [instantiate_tag_under q r] at right
  change Equiv pe Γ₀ δ (.let₁ (.bv 0) k.1) (instantiate k.1 (slot (Φ := Φ) (γ := γ) (A := packedExitType (A :: R))).1)
    (packedExitType L) at finish
  rw [instantiate_tag q (slot (γ := γ))] at finish
  exact ((Equiv.case (.refl scr) left right).symm.trans bind.symm).trans
    ((Equiv.let₁ (Equiv.caseEta scr) (.refl k.2.toHasType)).trans finish)

private theorem decoder_repack {i : Nat} {D : τ} (fallback : At L i D) (q : ExitSuffix L R)
    (s : Scope β γ) :
    Equiv pe Γ₀ (γ.snoc (packedExitType R)) ((decoder (Φ := Φ) fallback R q).render s).encode.toLetCase.1
      (q.inject (slot (γ := γ))).1 (packedExitType L) := by
  induction R generalizing m with
  | nil =>
    exact empty_context (((decoder fallback [] q).render s).encode.toLetCase.2.toHasType)
      (q.inject (slot (γ := γ))).2.toHasType
  | cons A R ih =>
    let δ := γ.snoc (packedExitType (A :: R))
    let payload : Operand Φ (δ.snoc A) A := slot
    have head := tag_head q payload
    have tail := ih q.tail (.skip s (packedExitType (A :: R)))
    rw [inject_tail q (slot (γ := δ))] at tail
    change Equiv pe Γ₀ δ
      (.case (.bv 0) (FiniteExit.tag L q.offset (Nat.add_zero q.offset ▸ q.at (i := 0) rfl) payload).1
        ((decoder fallback R q.tail).render (.skip s (packedExitType (A :: R)))).encode.toLetCase.1)
      _ (packedExitType L)
    rw [head]
    exact (Equiv.case (.refl .bv) (.refl (q.inject ⟨.inl payload.1, .inl payload.2⟩).2.toHasType) tail).trans
      (inject_case_eta (γ := γ) q)

theorem decoder_repack_proof {i : Nat} {D : τ} (fallback : At L i D) (s : Scope β γ) :
    Equiv pe Γ₀ (γ.snoc (packedExitType L))
      ((decoder (Φ := Φ) fallback L ExitSuffix.here).render s).encode.toLetCase.1
      (.bv 0) (packedExitType L) :=
  decoder_repack fallback ExitSuffix.here s

private theorem operand_base_term {A B : τ} (a : Operand Φ (β.snoc A) B) :
    ((Scope.base : Scope β β).operand a).1 = a.1 := by
  change rename (LetCase.LocallyNameless.Tm.up (fun i => i)) a.1 = _
  rw [LetCase.LocallyNameless.Tm.up_id, LetCase.LocallyNameless.Tm.rename_id]

theorem program_ofCode_replay (h : L ≠ []) (c : Code Φ β (packedExitType L)) :
    Equiv pe Γ₀ β (Program.ofCode h c).toLetCase.1 c.toLetCase.1 (packedExitType L) := by
  cases L with
  | nil => exact (h rfl).elim
  | cons A L =>
    have finish {m : Nat} {γ : BoundCtx τ m} (scope : Scope β γ) :=
      decoder_repack (Φ := Φ) (pe := pe) (rfl : At (A :: L) 0 A) (.here : ExitSuffix (A :: L) (A :: L)) scope
    have jump {X : τ} (a : Operand Φ (β.snoc X) (packedExitType (A :: L))) :
        Equiv pe Γ₀ (β.snoc X)
          ((Tree.jump a (.local (decoder (rfl : At (A :: L) 0 A) (A :: L) .here))).render .base).encode.toLetCase.1
          a.1 (packedExitType (A :: L)) := by
      let operand := (Scope.base : Scope β β).operand a
      have step := Equiv.let₁ (.refl operand.2.toHasType) (finish (.skip .base X))
      change Equiv pe Γ₀ (β.snoc X) (.let₁ operand.1 _) (.let₁ operand.1 (.bv 0)) _ at step
      have id := operand_base_term a
      change operand.1 = a.1 at id
      rw [id] at step
      exact (by
        change Equiv pe Γ₀ (β.snoc X) (.let₁ operand.1 _) a.1 _
        rw [id]
        exact step.trans (Equiv.letEta a.2.toHasType))
    cases c with
    | join a b => exact .let₁ (.refl a.toLetCase.2.toHasType) (jump b.toLetCase)
    | let₁ a b => exact .let₁ (.refl a.2.toHasType) (jump b.toLetCase)
    | br a =>
      exact (Equiv.let₁ (.refl a.2.toHasType) (finish .base)).trans (Equiv.letEta a.2.toHasType)
    | let₂ a b =>
      let d := (Code.let₂ a b).toLetCase.2.toHasType
      exact (Equiv.let₁ (.refl d) (finish .base)).trans (Equiv.letEta d)
    | case a l r =>
      let d := (Code.case a l r).toLetCase.2.toHasType
      exact (Equiv.let₁ (.refl d) (finish .base)).trans (Equiv.letEta d)

theorem ofLetCase_emit_proof {t : Term Φ n} (h : L ≠ [])
    (d : LetCase.LocallyNameless.Derivation Φ Γ₀ β t (packedExitType L)) :
    Equiv pe Γ₀ β (CheckedTable.ofLetCase h d).toLetCase.1 t (packedExitType L) := by
  let p := Program.ofCode h (Code.ofLetCase d)
  let witness : ResultGrammar p.toLetCase := ⟨p, rfl⟩
  have emitted := witness.toTable_toLetCase
  change Equiv pe Γ₀ β witness.toTable.toLetCase.1 t _
  rw [emitted]
  have eq := program_ofCode_replay (pe := pe) h (Code.ofLetCase d)
  rwa [Code.toLetCase_ofLetCase] at eq

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
