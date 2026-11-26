module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.OrderedPairs.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches HasType)
open Region.Paper
open Region.CfgEta.TypeCategory (returnRegion returnRegion_typed returnRegion_rename)
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.UnaryReturn.Beta.Constructors (pairSequence)
open Region.Paper.WithComputedCallReturns
open Morphism.CaseSSA (erase erase_hasType)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context Types)
open Silmaril.DeBruijn (lift)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

universe u v w

section Schedule

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A : τ} {r : Region Φ} {fs : List Φ}

theorem CallSchedule.valueBranches_proof (p : CallSchedule Γ r A fs) : ValueBranches Γ r [A] := by
  induction p with
  | ret value => exact .br (ℓ := 0) rfl value
  | call value _ ih => exact .let₁ (.op value.hasType) ih

omit [HasTy Φ τ] in
private theorem underValueBinder {Γ Δ : VCtx τ} {θ : Nat → Tm Φ}
    (values : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) (B : τ) :
    ∀ ⦃i T⦄, At (B :: Γ) i T → Tm.BranchValue (B :: Δ) (Tm.liftSubst θ i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact .var rfl
  | succ i =>
    change Tm.BranchValue (B :: Δ) ((θ i).rename Nat.succ) T
    rw [Tm.rename_eq_subst]
    exact (values hi).subst (fun _ _ atSlot => .var (Ren.wk Δ B atSlot))

theorem CallSchedule.subst_proof {Δ : VCtx τ} {θ : Nat → Tm Φ} (p : CallSchedule Γ r A fs)
    (values : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    CallSchedule Δ (r.substVars θ) A fs := by
  induction p generalizing Δ θ with
  | ret value => exact .ret (value.subst (fun _ _ hi => values hi))
  | call value _ ih =>
    exact .call (value.subst (fun _ _ hi => values hi)) (ih (underValueBinder values _))

theorem CallSchedule.rename_proof {Δ : VCtx τ} {ρ : Nat → Nat} (p : CallSchedule Γ r A fs)
    (typed : Ren Γ Δ ρ) : CallSchedule Δ (r.renameVars ρ) A fs := by
  rw [Region.renameVars_eq_substVars]
  exact p.subst_proof (fun _ _ hi => .var (typed hi))

/-- Native continuation substitution retains captures below each earlier reply
binder and concatenates exactly the two call lists. -/
theorem CallSchedule.splice_proof {B : τ} {s : Region Φ} {gs : List Φ}
    (p : CallSchedule Γ r A fs) (q : CallSchedule (A :: Γ) s B gs) :
    CallSchedule Γ (r.lsubst (fun _ => s)) B (fs ++ gs) := by
  induction p generalizing s with
  | ret value =>
    apply q.subst_proof
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact value
    | succ i => exact .var hi
  | @call Γ f a r A fs value cont ih =>
    exact .call value (ih (q.rename_proof ((Ren.wk Γ (instrTrg f)).lift A)))

theorem CallSchedule.pair_proof {B : τ} {s : Region Φ} {gs : List Φ}
    (p : CallSchedule Γ r A fs) (q : CallSchedule Γ s B gs) :
    CallSchedule Γ (r.lsubst (fun _ =>
      (s.renameVars Nat.succ).lsubst (fun _ => .br 0 (.pair (.var 1) (.var 0)))))
      (product A B) (fs ++ gs) := by
  have parts : Tm.BranchValue (B :: A :: Γ) (.pair (.var 1) (.var 0) : Tm Φ) (product A B) :=
    .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  simpa only [List.append_nil] using p.splice_proof
    ((q.rename_proof (Ren.wk Γ A)).splice_proof (.ret parts))

end Schedule

section Replay

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

omit [TypeFormers τ] in
private theorem atSingleton {A T : τ} {i : Nat} (hi : At [A] i T) : i = 0 ∧ T = A := by
  cases i with
  | zero => exact ⟨rfl, (Option.some.inj hi).symm⟩
  | succ i => simp [At] at hi

variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
  (base : ∀ {Γ r s L}, ConstructorJoin.Seed pe Γ r s L → Seed Γ r s L)

private theorem spliceEq {Γ : VCtx τ} {A B : τ} {r r' s s' : Region Φ}
    (guarded : ValueBranches Γ r [A]) (guarded' : ValueBranches Γ r' [A])
    (firstEq : Extension.Eqv Seed Γ r r' [A]) (cont : Extension.Eqv Seed (A :: Γ) s s' [B]) :
    Extension.Eqv Seed Γ (r.lsubst (fun _ => s)) (r'.lsubst (fun _ => s')) [B] := by
  have replace : Extension.Eqv Seed Γ (r.lsubst (fun _ => s)) (r.lsubst (fun _ => s')) [B] :=
    .lsubstCongr guarded (fun _ _ hi => (atSingleton hi).2.symm ▸ cont)
  exact replace.trans (.lsubstPost firstEq guarded guarded'
    (fun _ _ hi => (atSingleton hi).2.symm ▸ cont.typed.2))

include base in
private theorem returns_one {Γ : VCtx τ} {A : τ} {t : Tm Φ} (h : Tm.HasType Γ t A) :
    Extension.Eqv Seed Γ (returnRegion t) (returnOnce t) [A] :=
  UnaryReturn.returnRegion_eq_returnOnce (fun e => base (.inl (.inl (.inr (.inl e))))) h

include base in
private theorem assembly {n : Nat} {β : BoundCtx τ n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) (pure : ConstructorOnly (erase t)) :
    ∃ r, CallSchedule β.toList r A [] ∧ Extension.Eqv Seed β.toList (returnRegion (erase t)) r [A] := by
  obtain ⟨v, normal, _⟩ := constructor_replay pe ⟨t, d⟩ pure
  refine ⟨.br 0 v, .ret normal.typed.2, (returns_one pe base (erase_hasType d.toHasType)).trans ?_⟩
  exact WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed (fun e => base e)
    (ConstructorJoin.ofConstructor (WithConstructorSequencing.Joined.ofConstructor
      (WithConstructorSequencing.returnOnce_eq_branch normal)))

include base in
private theorem replay_pair {Γ : VCtx τ} {A B : τ} {a b : Tm Φ} {r s : Region Φ} {fs gs : List Φ}
    (includePair : ∀ {Γ r s L}, WithPairReturns.Step Γ r s L → Seed Γ r s L)
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B)
    (left : CallSchedule Γ r A fs) (right : CallSchedule Γ s B gs)
    (el : Extension.Eqv Seed Γ (returnRegion a) r [A])
    (er : Extension.Eqv Seed Γ (returnRegion b) s [B]) :
    Extension.Eqv Seed Γ (returnRegion (.pair a b))
      (r.lsubst (fun _ => (s.renameVars Nat.succ).lsubst (fun _ => .br 0 (.pair (.var 1) (.var 0)))))
      [product A B] := by
  let moved := hb.rename (Ren.wk Γ A)
  have er' := er.renameVars (Ren.wk Γ A)
  rw [← returnRegion_rename] at er'
  have gr := right.rename_proof (Ren.wk Γ A)
  have parts : Tm.BranchValue (B :: A :: Γ) (.pair (.var 1) (.var 0) : Tm Φ) (product A B) :=
    .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  have tail := spliceEq (UnaryReturn.returnOnce_valueBranches moved) gr.valueBranches_proof
    ((returns_one pe base moved).symm.trans er')
    (.refl (HasType.br (ℓ := 0) rfl parts.hasType) :
      Extension.Eqv Seed (B :: A :: Γ) (.br 0 (.pair (.var 1) (.var 0)))
        (.br 0 (.pair (.var 1) (.var 0))) [product A B])
  have contexts := spliceEq (UnaryReturn.returnOnce_valueBranches ha) left.valueBranches_proof
    ((returns_one pe base ha).symm.trans el) tail
  have split : Extension.Eqv Seed Γ (returnRegion (.pair a b))
      (pairSequence a b) [product A B] :=
    .extra (UnaryReturn.returnOnce_valueBranches (.pair ha hb)).hasType
      (WithPairReturns.pairSequence_typed ha hb).hasType (includePair (.seq ha hb))
  rw [show returnOnce a = (Region.br 0 a).bindBranchArguments from rfl,
    Region.lsubst_bindBranchArguments_br, show returnOnce (b.rename Nat.succ) =
      (Region.br 0 (b.rename Nat.succ)).bindBranchArguments from rfl,
    Region.lsubst_bindBranchArguments_br] at contexts
  exact split.trans contexts

private theorem operand_admitted {n : Nat} {β : BoundCtx τ n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (pairs : Bool) (d : Derivation Φ (.nil : Ctx Empty τ) β t A)
    (shape : CallOperand (erase t) pairs) : Operand.admittedDerivation d := by
  induction d with
  | let₁ _ _ iha ihb => exact ⟨iha shape.1, ihb shape.2⟩
  | let₂ | case => exact shape.elim
  | _ => trivial

include base in
private theorem normalize_operand {n : Nat} {β : BoundCtx τ n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (pairs : Bool)
    (includePair : pairs = true → ∀ {Γ r s L}, WithPairReturns.Step Γ r s L → Seed Γ r s L)
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) (shape : CallOperand (erase t) pairs) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase t) pairs) ∧
      Extension.Eqv Seed β.toList (returnRegion (erase t)) r [A] := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact assembly pe base .bv shape
  | unit => exact assembly pe base .unit shape
  | pair da db iha ihb =>
    cases pairs with
    | false => exact assembly pe base (.pair da db) shape
    | true =>
      obtain ⟨r, hr, el⟩ := iha shape.1
      obtain ⟨s, hs, er⟩ := ihb shape.2
      exact ⟨_, hr.pair_proof hs, replay_pair pe base (includePair rfl)
        (erase_hasType da.toHasType) (erase_hasType db.toHasType) hr hs el er⟩
  | inl a _ => exact assembly pe base (.inl a) shape
  | inr a _ => exact assembly pe base (.inr a) shape
  | @let₁ _ β a b A B da db iha ihb =>
    obtain ⟨r, hr, replayA⟩ := iha shape.1
    obtain ⟨s, hs, replayB⟩ := ihb shape.2
    have e := spliceEq (returnRegion_typed (erase_hasType da.toHasType))
      hr.valueBranches_proof replayA replayB
    exact ⟨_, hr.splice_proof hs, e⟩
  | @op _ β f a da ih =>
    obtain ⟨r, hr, replay⟩ := ih shape
    let next := returnRegion (Tm.op f (.var 0))
    have slot : Tm.BranchValue (instrSrc f :: β.toList) (.var 0 : Tm Φ) (instrSrc f) := .var rfl
    have run : CallSchedule (instrSrc f :: β.toList) next (instrTrg f) [f] :=
      .call slot (.ret (.var (i := 0) rfl))
    let step := WithComputedCallReturns.Step.seq f (erase_hasType da.toHasType)
    have moved : Extension.Eqv Seed _ _ _ _ :=
      .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (base (.inr step))
    have tail := spliceEq (returnRegion_typed (erase_hasType da.toHasType)) hr.valueBranches_proof replay
      (s := next) (.refl run.valueBranches_proof.hasType)
    exact ⟨_, hr.splice_proof run, moved.trans tail⟩
  | let₂ | case | abort => exact shape.elim

include base in
theorem operand_schedule_with_proof {n : Nat} {β : BoundCtx τ n} {A : τ} (pairs : Bool)
    (includePair : pairs = true → ∀ {Γ r s L}, WithPairReturns.Step Γ r s L → Seed Γ r s L)
    (a : Operand Φ β A) (shape : CallOperand (erase a.1) pairs) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase a.1) pairs) ∧
      Extension.Eqv Seed β.toList ((Code.br a).guardedSSA 0) r [A] ∧
      Extension.Eqv Seed β.toList ((Code.ofLetCase a.2).guardedSSA 0) r [A] := by
  obtain ⟨r, scheduled, replay⟩ := normalize_operand pe base pairs includePair a.2 shape
  have roundTrip := WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed (fun e => base e)
    (ConstructorJoin.ofConstructor (operand_roundTrip_constructor pe a (operand_admitted pairs a.2 shape)))
  have returned := (returns_one pe base (erase_hasType a.2.toHasType)).symm.trans replay
  exact ⟨r, scheduled, returned, roundTrip.symm.trans returned⟩

theorem code_admitted_proof {n : Nat} {β : BoundCtx τ n} {A : τ} (pairs : Bool) (c : Code Φ β A)
    (shape : CallOperand (erase c.toLetCase.1) pairs) : c.Admitted := by
  induction c with
  | br a => exact operand_admitted pairs a.2 shape
  | let₁ a _ ih => exact ⟨operand_admitted pairs a.2 shape.1, ih shape.2⟩
  | join _ _ iha ihb => exact ⟨iha shape.1, ihb shape.2⟩
  | let₂ | case => exact shape.elim

end Replay

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

theorem Endpoint.call_schedule_with_proof {Seed : VCtx Types → Region Φ → Region Φ → LCtx Types → Prop}
    (pairs : Bool) (base : ∀ {Γ r s L}, ConstructorJoin.Seed false Γ r s L → Seed Γ r s L)
    (includePair : pairs = true → ∀ {Γ r s L}, WithPairReturns.Step Γ r s L → Seed Γ r s L)
    (p : Endpoint Φ β A) (guarded : ValueBranches β.toList p.region [A])
    (shape : CallOperand (erase p.compile.1) pairs) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase p.compile.1) pairs) ∧
      Extension.Eqv Seed β.toList p.region r [A] := by
  obtain ⟨r, order, _, replay⟩ := operand_schedule_with_proof false base pairs includePair p.compile shape
  have roundTrip := p.joined_roundTrip (code_admitted_proof pairs p.code shape) guarded
  have included := WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed (fun e => base e)
    (ConstructorJoin.ofConstructor (WithConstructorSequencing.Joined.ofJoined roundTrip))
  exact ⟨r, order, included.trans replay⟩

theorem Endpoint.call_sound_proof {p q : Endpoint Φ β A} (h : p.CallEqv q) : p.Valid q := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr regionCoherent _ shared
  exact ConstructorJoin.sound J M shared h p.typed q.typed

theorem Endpoint.pair_call_sound_proof {p q : Endpoint Φ β A} (h : p.PairCallEqv q) : p.Valid q := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr regionCoherent _ shared
  exact OrderedPairs.sound J M shared h p.typed q.typed

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
