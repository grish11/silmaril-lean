module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Prefix.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.Reflection
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms

/-! # One-request steps in any coherent trace model, and the request-prefix model -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Exits model Trace modelCoherent Event request)
open Paper.WithCaseBind.BitQuery.RequestTree
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_postcomp)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext_of)
open Silmaril.Semantics.NondeterministicTrace (Tagged Finite)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

set_option backward.isDefEq.respectTransparency false

section Monad

variable {A B : Type}

/-- Two steps with the same complete outcomes, one of which only adds
incomplete observations, have the same complete runs. -/
theorem iter_ok_congr (f f' : A → Trace (B ⊕ A))
    (sub : ∀ a, (f a).outcomes ⊆ (f' a).outcomes)
    (ok : ∀ a y w, (Except.ok y, w) ∈ (f' a).outcomes → (Except.ok y, w) ∈ (f a).outcomes)
    (a : A) (b : B) (w : Word) :
    (Except.ok b, w) ∈ (Silmaril.Elgot.iter f' a).outcomes ↔
      (Except.ok b, w) ∈ (Silmaril.Elgot.iter f a).outcomes := by
  constructor
  · intro h
    refine iter_induction f'
      (fun s => {obs | ∀ b, obs.1 = Except.ok b → (Except.ok b, obs.2) ∈ (Silmaril.Elgot.iter f s).outcomes})
      ?_ ?_ ?_ a h b rfl
    · intro s t w _ b h
      cases h
    · intro s b w hw b' h
      cases h
      exact (iter_unfold f s).2 (.inr (.inl ⟨b, rfl, ok s _ _ hw⟩))
    · intro s next u r v hu hv b h
      exact (iter_unfold f s).2 (.inr (.inr ⟨next, u, v, ok s _ _ hu, hv b h, rfl⟩))
  · intro h
    refine iter_induction f (fun s => (Silmaril.Elgot.iter f' s).outcomes) ?_ ?_ ?_ a h
    · intro s t w hw
      exact (iter_unfold f' s).2 (.inl ⟨t, rfl, sub s hw⟩)
    · intro s b w hw
      exact (iter_unfold f' s).2 (.inr (.inl ⟨b, rfl, sub s hw⟩))
    · intro s next u r v hu hv
      exact (iter_unfold f' s).2 (.inr (.inr ⟨next, u, v, sub s hu, hv, rfl⟩))

end Monad

theorem leaf_typed {Γ : VCtx (Ty Empty)} (again : Bool) :
    ValueBranches (Bit :: Γ) (.br (if again then 1 else 0) (.var 0) : Region signature.Instr) Exits :=
  .br (exit_typed again) (.var (i := 0) rfl)

theorem ask_typed (l fl fr : Bool) :
    ValueBranches [Bit]
      (.case (.op (show signature.Instr from .ask l) (.var 0))
        (.br (if fl then 1 else 0) (.var 0)) (.br (if fr then 1 else 0) (.var 0)) : Region signature.Instr)
      Exits :=
  .case (.op (.var (i := 0) rfl)) (leaf_typed fl) (leaf_typed fr)

theorem oneAsk_written (l fl fr : Bool) :
    (oneAsk l fl fr).written =
      .case (.op (show signature.Instr from .ask l) (.var 0))
        (.br (if fl then 1 else 0) (.var 0)) (.br (if fr then 1 else 0) (.var 0)) := by
  cases fl <;> cases fr <;> rfl

section Coherent

-- The instruction interpretation is the parameter of this section.
set_option linter.concreteInstances false

variable [inst : InstructionModel J M signature.Instr] [RegionTypingCoherent (Φ := signature.Instr) J M]

noncomputable abbrev runE {Γ : VCtx (Ty Empty)} {r : Region signature.Instr}
    (h : ValueBranches Γ r Exits) (x : ctxObj M Γ) : Trace (value (packedExitType Exits)) :=
  (denoteRegion J M h.hasType ≫ (J).map (packLabel M Exits)).of x

theorem packed_run {r : Region signature.Instr} (hr : ValueBranches [Bit] r Exits) (x : value Bit) :
    (denoteSingletonRegion J M hr.packExits.hasType).of x = runE hr (PUnit.unit, x) := by
  unfold denoteSingletonRegion
  change (((J).map _ ≫ denoteRegion J M hr.hasType.packExits ≫ (J).map _)).of x = _
  rw [denoteRegion_packExits_valueBranches J M (fun _ _ => ⟨rfl, rfl⟩) hr]
  have combine : packLabelExit M Exits ≫ singletonLabelPayload M (packedExitType Exits) =
      packLabel M Exits := by
    unfold packLabelExit
    rw [Category.assoc, SingletonDispatcher.labelInject_payload, Category.comp_id]
  simp only [Category.assoc, ← (J).map_comp, combine]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure (PUnit.unit, x)) (fun y => runE hr y) = _
  rw [pure_bind]

theorem case_run {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {a : Tm signature.Instr}
    {l r : Region signature.Instr} {ha : Tm.HasType Γ a (coprod A B)}
    {sa : (J).obj (ctxObj M Γ) ⟶ (J).obj (value (coprod A B))}
    (d : Denotes J M ha sa) (hl : ValueBranches (A :: Γ) l Exits)
    (hr : ValueBranches (B :: Γ) r Exits) (x : ctxObj M Γ) :
    runE (.case ha hl hr) x =
      Bind.bind (m := Trace) (sa.of x)
        (fun | .inl a => runE hl (x, a) | .inr b => runE hr (x, b)) := by
  have h := RegionDenotes.eq_denote J M
    (.case d (denoteRegion_spec J M hl.hasType) (denoteRegion_spec J M hr.hasType))
  unfold runE
  erw [← h, case_postcomp J, caseWithContext_of (m := Trace)]
  simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  have coord (v : value (coprod A B)) :
      (Types.binaryCoproductIso ((M).obj A) ((M).obj B)).hom (((M).coprodIso A B).hom v) = v :=
    ConcreteCategory.congr_hom (Types.binaryCoproductIso (value A) (value B)).inv_hom_id v
  change Bind.bind (m := Trace) (Bind.bind (m := Trace) (sa.of x)
    (fun v => pure (((M).coprodIso A B).hom v))) _ = _
  simp only [bind_assoc, pure_bind, coord]
  congr 1
  funext reply
  cases reply <;> rfl

theorem leaf_run {Γ : VCtx (Ty Empty)} (x : ctxObj M Γ) {i : Nat} (hi : At Γ i Bit) (again : Bool) :
    runE (.br (exit_typed again) (.var hi)) x = pure (leafValue again ((lookup M i hi) x)) := by
  unfold runE
  have d := RegionDenotes.eq_denote J M
    (RegionDenotes.br (h := exit_typed again)
      (Denotes.var («J» := J) («M» := M) (Φ := signature.Instr) hi))
  erw [← d]
  have comp := (J).map_comp (labelInject M _ (exit_typed again)) (packLabel M Exits)
  erw [Category.assoc, ← comp, labelInject_packLabel, Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure ((lookup M i hi) x))
    (fun y => pure ((packedLabelInject M _ (exit_typed again)) y)) = _
  rw [pure_bind]
  apply congrArg (pure (f := Trace))
  cases again
  · simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Bool.false_eq_true, ite_false]
    exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom
      (value Bit) (value (packedExitType [Bit]))) ((lookup M i hi) x)
  · simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Category.assoc, ite_true]
    have inner := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType ([] : LCtx (Ty Empty)))))
      ((lookup M i hi) x)
    have outer := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_hom (value Bit) (value (packedExitType [Bit])))
        (Sum.inl ((lookup M i hi) x) : value (packedExitType [Bit]))
    change (coprod.inr ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType [Bit]))).hom)
      ((coprod.inl ≫ (Types.binaryCoproductIso (value Bit)
        (value (packedExitType ([] : LCtx (Ty Empty))))).hom) ((lookup M i hi) x)) = _
    rw [inner]
    exact outer

/-- The primitive of the interpretation, as a computation of the trace monad. -/
noncomputable abbrev opRun (l : Bool) (x : value Bit) : Trace (value Answer) :=
  (inst.denote (show signature.Instr from .ask l)).of x

theorem ask_run (l fl fr : Bool) (x : value Bit) :
    runE (ask_typed l fl fr) (PUnit.unit, x) = (opRun l x >>= fun ans => pure (route fl fr ans)) := by
  let op : signature.Instr := .ask l
  have d : Denotes J M (.op (f := op) (.var (i := 0) (rfl : At [Bit] 0 Bit)))
      ((J).map (lookup M 0 (rfl : At [Bit] 0 Bit)) ≫ inst.denote op) :=
    .op (.var rfl)
  refine (case_run d (leaf_typed fl) (leaf_typed fr) (PUnit.unit, x)).trans ?_
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (Bind.bind (m := Trace) (pure x) (fun y => (inst.denote op).of y)) _ = _
  rw [pure_bind]
  congr 1
  funext reply
  cases reply
  · exact leaf_run (Γ := [Bit, Bit]) _ (rfl : At [Bit, Bit] 0 Bit) fl
  · exact leaf_run (Γ := [Bit, Bit]) _ (rfl : At [Bit, Bit] 0 Bit) fr

theorem stepIn_written {p : Program} {r : Region signature.Instr} (eq : p.written = r)
    (hr : ValueBranches [Bit] r Exits) (x : value Bit) :
    stepIn p (Sum.inl x) = runE hr (PUnit.unit, x) := by
  subst eq
  exact packed_run p.typed x

/-- A one-request step sends the request on the state and routes the reply. -/
theorem oneAsk_step (l fl fr : Bool) (x : value Bit) :
    stepIn (oneAsk l fl fr) (Sum.inl x) = (opRun l x >>= fun ans => pure (route fl fr ans)) :=
  (stepIn_written (oneAsk_written l fl fr) (ask_typed l fl fr) x).trans (ask_run l fl fr x)

/-- The silent step repeats with its state and sends nothing. -/
theorem spin_step (x : value Bit) :
    stepIn spin (Sum.inl x) = (pure (Sum.inr (Sum.inl x)) : Trace (value Bit ⊕ value State)) :=
  (stepIn_written (r := .br (if true then 1 else 0) (.var 0)) rfl
    (.br (exit_typed true) (.var (i := 0) rfl)) x).trans
      (leaf_run (Γ := [Bit]) (PUnit.unit, x) (rfl : At [Bit] 0 Bit) true)

/-- A model of this form that separates two typed regions refutes validity. -/
theorem not_valid_of_ne {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {r s : Region signature.Instr}
    (hr : HasType Γ r L) (hs : HasType Γ s L) (ne : denoteRegion J M hr ≠ denoteRegion J M hs) :
    ¬ Valid hr hs :=
  fun h => ne (h J M (fun _ _ => ⟨rfl, rfl⟩))

end Coherent

/-! ## The four-reply model on one-request steps -/

theorem complete_oneAsk_step (l fl fr : Bool) (x : value Bit) :
    stepModel (oneAsk l fl fr) (Sum.inl x) = (request l x >>= fun ans => pure (route fl fr ans)) :=
  @oneAsk_step (instructions model) modelCoherent l fl fr x

theorem poll_oneAsk (a : Poll) : a.program = oneAsk a.label a.returnRight (!a.returnRight) := by
  obtain ⟨l, rr⟩ := a
  cases rr <;> rfl

theorem askSpin_oneAsk (l : Bool) : askSpin l = oneAsk l true true := rfl

/-! ## The request-prefix model -/

noncomputable local instance : InstructionModel J M signature.Instr := instructions prefixModel
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

theorem prefix_oneAsk_step (l fl fr : Bool) (x : value Bit) :
    prefixStep (oneAsk l fl fr) (Sum.inl x) =
      (prefixRequest l x >>= fun ans => pure (route fl fr ans)) :=
  oneAsk_step l fl fr x

theorem prefix_spin_step (x : value Bit) :
    prefixStep spin (Sum.inl x) = (pure (Sum.inr (Sum.inl x)) : Trace (value Bit ⊕ value State)) :=
  spin_step x

theorem prefixObservations_eq (p : Program) (g : Bool) :
    prefixObservations p g =
      (Silmaril.Elgot.iter (m := Trace) (prefixStep p) (Sum.inl (bit g))).outcomes :=
  congrArg Tagged.outcomes (loop_run_in p (Sum.inl (bit g)))

theorem prefixRequest_outcomes (l : Bool) (q : value Bit) :
    (prefixRequest l q).outcomes = (request l q).outcomes ∪ {(Except.error l, 1)} := by
  unfold prefixRequest Tagged.withIncomplete
  rw [Tagged.outcomes_ofOutcomes, Set.image_singleton]

theorem bind_sub {A : Type} (l : Bool) (q : value Bit) (k : value Answer → Trace A) :
    (request l q >>= k).outcomes ⊆ (prefixRequest l q >>= k).outcomes := by
  rintro ⟨r, w⟩ h
  rw [Tagged.mem_bind] at h ⊢
  rcases h with ⟨t, rfl, ht⟩ | ⟨a, u, v, ha, hk, rfl⟩
  · exact .inl ⟨t, rfl, by rw [prefixRequest_outcomes]; exact .inl ht⟩
  · exact .inr ⟨a, u, v, by rw [prefixRequest_outcomes]; exact .inl ha, hk, rfl⟩

theorem bind_ok {A : Type} (l : Bool) (q : value Bit) (k : value Answer → Trace A) {y : A} {w : Word}
    (h : (Except.ok y, w) ∈ (prefixRequest l q >>= k).outcomes) :
    (Except.ok y, w) ∈ (request l q >>= k).outcomes := by
  rw [Tagged.mem_bind] at h ⊢
  rcases h with ⟨t, bad, -⟩ | ⟨a, u, v, ha, hk, rfl⟩
  · cases bad
  · rw [prefixRequest_outcomes] at ha
    rcases ha with ha | bad
    · exact .inr ⟨a, u, v, ha, hk, rfl⟩
    · cases (Prod.mk.inj (Set.mem_singleton_iff.1 bad)).1

/-- On a one-request program the complete returns of the two models agree. -/
theorem prefix_complete_iff (l fl fr g : Bool) (b : value Bit) (w : Word) :
    (Except.ok b, w) ∈ prefixObservations (oneAsk l fl fr) g ↔
      (Except.ok b, w) ∈ loopObservations (oneAsk l fl fr) g := by
  rw [prefixObservations_eq, loopObservations_eq]
  refine iter_ok_congr (stepModel (oneAsk l fl fr)) (prefixStep (oneAsk l fl fr)) ?_ ?_ _ b w
  · rintro (x | e)
    · rw [complete_oneAsk_step, prefix_oneAsk_step]
      exact bind_sub l x _
    · exact e.elim
  · rintro (x | e) y w h
    · rw [prefix_oneAsk_step] at h
      rw [complete_oneAsk_step]
      exact bind_ok l x _ h
    · exact e.elim

theorem prefix_poll_complete (a : Poll) (g : Bool) (b : value Bit) (w : Word) :
    (Except.ok b, w) ∈ prefixObservations a.program g ↔ (Except.ok b, w) ∈ loopObservations a.program g := by
  rw [poll_oneAsk]
  exact prefix_complete_iff _ _ _ g b w

/-- The first request of the always-requesting loop is observed pending. -/
theorem askSpin_pending (l g : Bool) :
    (Except.error l, (1 : Word)) ∈ prefixObservations (askSpin l) g := by
  rw [prefixObservations_eq, iter_unfold]
  refine .inl ⟨l, rfl, ?_⟩
  rw [askSpin_oneAsk, prefix_oneAsk_step, Tagged.mem_bind]
  exact .inl ⟨l, rfl, by rw [prefixRequest_outcomes]; exact .inr rfl⟩

/-- After one completed exchange the next request is pending, sent with
that reply's payload. The log holds the completed exchange. -/
theorem askSpin_pending_after (l g tag pl : Bool) :
    (Except.error l, FreeMonoid.of (event l g (tag, pl)) * 1) ∈ prefixObservations (askSpin l) g := by
  rw [prefixObservations_eq, iter_unfold]
  refine .inr (.inr ⟨Sum.inl (bit pl), _, _, ?_, ?_, rfl⟩)
  · rw [askSpin_oneAsk, prefix_oneAsk_step, Tagged.mem_bind]
    refine .inr ⟨answer tag pl, _, 1, ?_, mem_pure.2 ⟨?_, rfl⟩, mul_one _⟩
    · rw [prefixRequest_outcomes]
      refine .inl ⟨(tag, pl), ?_⟩
      cases g <;> rfl
    · cases tag <;> rfl
  · rw [← prefixObservations_eq]
    exact askSpin_pending l pl

theorem spin_prefix_empty (g : Bool) : prefixObservations spin g = ∅ := by
  rw [prefixObservations_eq]
  refine Set.eq_empty_of_subset_empty (iter_induction (prefixStep spin) (fun _ => ∅) ?_ ?_ ?_ _)
  · rintro (x | e) t w hw
    · rw [prefix_spin_step] at hw
      cases (mem_pure.1 hw).1
    · exact e.elim
  · rintro (x | e) b w hw
    · rw [prefix_spin_step] at hw
      cases (mem_pure.1 hw).1
    · exact e.elim
  · intro s next u r v _ hv
    exact hv.elim

/-- The request-prefix model separates the two literal loops, so they
are not valid. -/
theorem askSpin_not_valid (l : Bool) :
    ¬ Valid (loop_typed (askSpin l)).hasType (loop_typed spin).hasType := by
  refine not_valid_of_ne _ _ (fun eq => ?_)
  have obs : prefixObservations (askSpin l) false = prefixObservations spin false := by
    unfold prefixObservations denoteSingletonRegion
    rw [eq]
  have pending := askSpin_pending l false
  rw [obs, spin_prefix_empty] at pending
  exact pending

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop
