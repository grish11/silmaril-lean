module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TwoBitQueries

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.TwoRequests
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit answer)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)

local notation "U" => (Ty.unit : Ty Empty)
local notation "E" => Paper.Extension.Eqv Seed

private theorem weaken_subst (t : Tm signature.Instr) (σ : Nat → Tm signature.Instr) :
    (t.rename Nat.succ).subst (Tm.liftSubst σ) = (t.subst σ).rename Nat.succ := by
  rw [Tm.subst_rename, Tm.rename_subst]
  rfl

private theorem compile_subst (label : Bool) {n : Nat} (e : Expr n)
    (slots : Fin n → Tm signature.Instr) (σ : Nat → Tm signature.Instr) :
    (compile label e slots).substVars σ = compile label e (fun i => (slots i).subst σ) := by
  induction e generalizing σ with
  | literal b => cases b <;> rfl
  | read i => rfl
  | split l r ihl ihr =>
    simp only [compile, Region.substVars, ihl, ihr, weaken_subst]

private theorem case_constructor {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr}
    {l r : Region signature.Instr} (b : Bool) (ha : Tm.HasType Γ a U)
    (hl : ValueBranches (U :: Γ) l Exits) (hr : ValueBranches (U :: Γ) r Exits) :
    E Γ (.case (constructorBit b a) l r) (.let₁ a (if b then r else l)) Exits := by
  cases b
  · exact .paper (.cfgEta (.native (.base (.caseInl ha hl.hasType hr.hasType))))
  · exact .paper (.cfgEta (.native (.base (.caseInr ha hl.hasType hr.hasType))))

private theorem drop_call_binder {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a U) (label b : Bool) :
    E Γ (.let₁ a (call label (literal b))) (call label (literal b)) Exits := by
  cases b <;> exact .paper (.cfgEta (.native (.letValue ha
    (call_typed label (constructorBit_value _ .unit).hasType).hasType)))

private theorem compile_known (label : Bool) {n : Nat} (e : Expr n) (env : Assignment n)
    {Γ : VCtx (Ty Empty)} (payload : Fin n → Tm signature.Instr)
    (hp : ∀ i, Tm.BranchValue Γ (payload i) U) :
    E Γ (compile label e (fun i => constructorBit (env i) (payload i)))
      (call label (literal (e.eval env))) Exits := by
  induction e generalizing Γ with
  | literal b => exact .refl (call_typed label (constructorBit_value b .unit).hasType).hasType
  | read i =>
    refine (case_constructor (env i) (hp i).hasType
      (call_typed label (.inl .unit)) (call_typed label (.inr .unit))).trans ?_
    cases eq : env i
    · simp only [Expr.eval, eq, Bool.false_eq_true, ite_false]
      exact drop_call_binder (hp i) label false
    · simp only [Expr.eval, eq, ite_true]
      exact drop_call_binder (hp i) label true
  | @split n l r ihl ihr =>
    let older := fun (i : Fin n) => (payload i.succ).rename Nat.succ
    have ht (i) : Tm.BranchValue (U :: Γ) (older i) U := by
      unfold older
      rw [Tm.rename_eq_subst]
      exact (hp i.succ).subst (fun _ _ hi => .var (Ren.wk Γ U hi))
    have rename (i) : (constructorBit (env i.succ) (payload i.succ)).rename Nat.succ =
        constructorBit (env.tail i) (older i) := by
      change (constructorBit (env i.succ) (payload i.succ)).rename Nat.succ =
        constructorBit (env i.succ) ((payload i.succ).rename Nat.succ)
      cases env i.succ <;> rfl
    simp only [compile, rename]
    refine (case_constructor (env 0) (hp 0).hasType
      (compile_typed _ _ (fun i => (constructorBit_value _ (ht i)).hasType))
      (compile_typed _ _ (fun i => (constructorBit_value _ (ht i)).hasType))).trans ?_
    cases h : env 0
    · simpa only [Expr.eval, h, Bool.false_eq_true, ite_false] using
        (Paper.Extension.Eqv.let₁ (hp 0).hasType (ihl env.tail older ht)).trans
          (drop_call_binder (hp 0) label (l.eval env.tail))
    · simpa only [Expr.eval, h, ite_true] using
        (Paper.Extension.Eqv.let₁ (hp 0).hasType (ihr env.tail older ht)).trans
          (drop_call_binder (hp 0) label (r.eval env.tail))

private def beforeReplyCase (guard : Bool) : Fin 2 → Tm signature.Instr :=
  Fin.cases (.var 0) (fun _ => constructorBit guard (.var 2))

private def knownPayloads : Fin 2 → Tm signature.Instr :=
  Fin.cases (.var 0) (fun _ => .var 2)

private theorem extract_query (label : Bool) (e : Expr 2) (guard reply : Bool) :
    E [U, Bit, U, Bit]
      ((compile label e (beforeReplyCase guard)).substVars
        (Tm.replaceNewest (constructorBit reply (.var 0))))
      (call label (literal (e.eval (assignment guard reply)))) Exits := by
  rw [compile_subst]
  have slots : (fun i => (beforeReplyCase guard i).subst
      (Tm.replaceNewest (constructorBit reply (.var 0)))) =
      (fun i => constructorBit (assignment guard reply i) (knownPayloads i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · cases reply <;> rfl
    · rw [Fin.eq_zero j]
      cases guard <;> rfl
  rw [slots]
  exact compile_known label e (assignment guard reply) knownPayloads
    (fun i => Fin.cases (.var (i := 0) rfl) (fun _ => .var (i := 2) rfl) i)

private theorem replay_row (label : Bool) (query : Expr 2) (guard : Bool) :
    E [Bit, U, Bit]
      (compile label query (guardedSlots guard))
      (compile label (Expr.quote 1 (fun env => query.eval (assignment guard (env 0)))) replySlot) Exits := by
  let body := compile label query (beforeReplyCase guard)
  have ht : ValueBranches [Bit, Bit, U, Bit] body Exits :=
    compile_typed _ _ (fun i => Fin.cases (.var (i := 0) rfl)
      (fun _ => (constructorBit_value guard (.var (i := 2) rfl)).hasType) i)
  have unroll : E [Bit, U, Bit]
      (.case (.var 0)
        (body.substVars (Tm.replaceNewest (constructorBit false (.var 0))))
        (body.substVars (Tm.replaceNewest (constructorBit true (.var 0)))))
      (body.substVars (Tm.singleSubst (.var 0))) Exits :=
    .paper (.cfgEta (.native (.caseValue (.var (i := 0) rfl) ht.hasType)))
  have reduced : body.substVars (Tm.singleSubst (.var 0)) =
      compile label query (guardedSlots guard) := by
    unfold body
    rw [compile_subst]
    congr 1
    funext i
    refine Fin.cases rfl (fun _ => ?_) i
    cases guard <;> rfl
  rw [reduced] at unroll
  exact unroll.symm.trans (.case (.var (i := 0) rfl)
    (extract_query label query guard false)
    (extract_query label query guard true))

theorem packed_replay (p : Program) : p.packed = p.key.packed := by
  have step (guard : Bool) : E [U, Bit]
      (first p.firstLabel guard (compile p.secondLabel p.secondQuery (guardedSlots guard)))
      (first p.firstLabel guard (compile p.secondLabel (p.key.row guard) replySlot)) Exits :=
    .case (.op (constructorBit_value guard .unit).hasType) (replay_row p.secondLabel p.secondQuery guard) (replay_row p.secondLabel p.secondQuery guard)
  have eq : E [Bit] p.region p.key.region Exits :=
    .case (.var (i := 0) rfl) (step false) (step true)
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
    (eq.lsubstPost p.typed p.key.typed (fun _ _ hi =>
      (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hi).hasType))

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Paper.WithCaseBind.BitQuery.Execution
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Answer)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open scoped MonoidalCategory

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

private theorem test_run {Γ : VCtx (Ty Empty)} {l r : Region signature.Instr}
    (hl : ValueBranches (U :: Bit :: Γ) l Exits) (hr : ValueBranches (U :: Bit :: Γ) r Exits)
    (x : ctxObj M Γ) (b : Bool) :
    runAt (.case (.var (i := 0) rfl) hl hr) (x, bit b) =
      if b then runAt hr ((x, bit b), PUnit.unit) else runAt hl ((x, bit b), PUnit.unit) := by
  have h := case_run (Denotes.var («J» := Kleisli.J (m := Trace)) («M» := Kleisli.types) (i := 0) rfl)
    hl hr (x, bit b)
  change runAt (.case (.var (i := 0) rfl) hl hr) (x, bit b) =
    Bind.bind (m := Trace) (pure (bit b)) _ at h
  erw [h, pure_bind]
  cases b <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem branch_run {Γ : VCtx (Ty Empty)} (x : ctxObj M Γ) (v : value Bit)
    (i : Nat) (hi : At Exits i Bit) :
    runAt (Γ := Bit :: Γ) (.br hi (.var (i := 0) rfl)) (x, v) = pure ((packedLabelInject M i hi) v) := by
  unfold runAt
  have d := RegionDenotes.eq_denote J M
    (RegionDenotes.br (h := hi) (Denotes.var («J» := Kleisli.J (m := Trace)) («M» := Kleisli.types)
      (Φ := signature.Instr) (i := 0) (rfl : At (Bit :: Γ) 0 Bit)))
  erw [← d]
  have comp := (J).map_comp (labelInject M i hi) (packLabel M Exits)
  erw [Category.assoc, ← comp, labelInject_packLabel, Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure v) (fun y => pure ((packedLabelInject M i hi) y)) = _
  rw [pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem call_run {Γ : VCtx (Ty Empty)} (label b : Bool) (x : ctxObj M Γ) :
    runAt (call_typed label (constructorBit_value b .unit).hasType) x =
      (request label (bit b) >>= fun reply => pure (atExit reply)) := by
  let left : ValueBranches (Φ := signature.Instr) (Bit :: Γ) (.br 0 (.var 0)) Exits := .br rfl (.var (i := 0) rfl)
  let right : ValueBranches (Φ := signature.Instr) (Bit :: Γ) (.br 1 (.var 0)) Exits := .br rfl (.var (i := 0) rfl)
  refine (request_case_run label b left right x).trans ?_
  congr 1
  funext reply
  cases reply with
  | inl v =>
    change runAt left (x, v) = pure (atExit (.inl v))
    erw [branch_run x v 0 (rfl : At Exits 0 Bit)]
    congr 1
    simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
    exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom
      (value Bit) (value (packedExitType [Bit]))) v
  | inr v =>
    change runAt right (x, v) = pure (atExit (.inr v))
    erw [branch_run x v 1 (rfl : At Exits 1 Bit)]
    congr 1
    simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Category.assoc]
    have inner := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType []))) v
    have outer := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_hom (value Bit) (value (packedExitType [Bit])))
        (Sum.inl v : value (packedExitType [Bit]))
    change (coprod.inr ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType [Bit]))).hom)
      ((coprod.inl ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType []))).hom) v) = _
    rw [inner]
    exact outer

private def replyFields : value Answer → Reply
  | .inl a => (false, queryBit a)
  | .inr a => (true, queryBit a)

private theorem replyFields_answer (reply : Reply) : replyFields (answer reply.1 reply.2) = reply := by
  obtain ⟨right, b⟩ := reply
  cases right <;> cases b <;> rfl

private theorem row_run (label : Bool) (table : Bool → Bool) (x : ctxObj M [U, Bit]) (a : value Bit) :
    runAt (compile_typed label (Expr.quote 1 (fun env => table (env 0))) (Γ := [Bit, U, Bit]) (slots := replySlot) (fun _ => .var (i := 0) rfl))
        (x, a) =
      (request label (bit (table (queryBit a))) >>=
        fun r => pure (atExit r)) := by
  have execute (b : Bool) : runAt
      (compile_typed label (Expr.quote 1 (fun env => table (env 0))) (Γ := [Bit, U, Bit]) (slots := replySlot) (fun _ => .var (i := 0) rfl))
      (x, bit b) =
      (request label (bit (table (queryBit (bit b)))) >>=
        fun r => pure (atExit r)) := by
    let next (r : Bool) := call_typed label (Γ := [U, Bit, U, Bit])
      (constructorBit_value (table r) .unit).hasType
    refine (test_run (next false) (next true) x b).trans ?_
    cases b <;> exact call_run _ _ _
  cases a with
  | inl u => cases u; exact execute false
  | inr u => cases u; exact execute true

private theorem key_run (k : Key) (g : Bool) :
    (denote.map k.packed).of (bit g) =
      (request k.firstLabel (bit g) >>= fun firstReply =>
        request k.secondLabel (bit (k.secondQuery (assignment g (replyFields firstReply).2))) >>= fun secondReply =>
          pure (atExit secondReply)) := by
  refine (run_packed k.typed g).trans ?_
  have execute (b : Bool) :
      runAt (first_typed k.firstLabel b
        (compile_typed k.secondLabel (k.row b) (Γ := [Bit, U, Bit]) (slots := replySlot) (fun _ => .var (i := 0) rfl)))
        ((PUnit.unit, bit b), PUnit.unit) =
      (request k.firstLabel (bit b) >>= fun firstReply =>
        request k.secondLabel (bit (k.secondQuery (assignment b (replyFields firstReply).2))) >>= fun secondReply =>
          pure (atExit secondReply)) := by
    let next := compile_typed k.secondLabel (k.row b) (Γ := [Bit, U, Bit]) (slots := replySlot)
      (fun _ => .var (i := 0) rfl)
    refine (request_case_run k.firstLabel b next next ((PUnit.unit, bit b), PUnit.unit)).trans ?_
    congr 1
    funext a
    cases a
    all_goals exact row_run k.secondLabel (fun r => k.secondQuery (assignment b r)) _ _
  let arm (b : Bool) := first_typed k.firstLabel b
    (compile_typed k.secondLabel (k.row b) (Γ := [Bit, U, Bit]) (slots := replySlot)
      (fun _ => .var (i := 0) rfl))
  refine (test_run (Γ := []) (arm false) (arm true) PUnit.unit g).trans ?_
  cases g <;> exact execute _

private theorem two_request_outcomes (label g : Bool) (next : Reply → Bool × Bool) :
    (request label (bit g) >>= fun firstReply =>
      request (next (replyFields firstReply)).1 (bit (next (replyFields firstReply)).2) >>= fun secondReply =>
        pure (atExit secondReply)).outcomes =
      Set.range fun pair : Reply × Reply =>
        (.ok (atExit (answer pair.2.1 pair.2.2)),
          FreeMonoid.of ⟨label, g, pair.1.1, pair.1.2⟩ *
          FreeMonoid.of ⟨(next pair.1).1, (next pair.1).2, pair.2.1, pair.2.2⟩) := by
  apply Set.ext
  rintro ⟨result, word⟩
  rw [bind_request]
  constructor
  · rintro ⟨firstReply, tail, h, wordEq⟩
    simp only [replyFields_answer] at h
    rw [bind_request] at h
    obtain ⟨secondReply, done, hp, tailEq⟩ := h
    have hp' : (result, done) = (.ok (atExit (answer secondReply.1 secondReply.2)), 1) := hp
    rcases Prod.mk.inj hp' with ⟨resultEq, doneEq⟩
    refine ⟨(firstReply, secondReply), Prod.ext resultEq.symm ?_⟩
    change FreeMonoid.of (⟨label, g, firstReply.1, firstReply.2⟩ : Event) *
      FreeMonoid.of ⟨(next firstReply).1, (next firstReply).2, secondReply.1, secondReply.2⟩ = word
    rw [← wordEq, ← tailEq, doneEq, mul_one]
  · rintro ⟨⟨firstReply, secondReply⟩, h⟩
    cases h
    refine ⟨firstReply, FreeMonoid.of ⟨(next firstReply).1, (next firstReply).2,
      secondReply.1, secondReply.2⟩, ?_, rfl⟩
    simp only [replyFields_answer]
    rw [bind_request]
    exact ⟨secondReply, 1, rfl, mul_one _⟩

private theorem key_outcomes (k : Key) (g : Bool) : k.observations g = k.outcomes g := by
  unfold Key.observations
  refine (congrArg (Tagged.outcomes (A := value (packedExitType Exits))) (key_run k g)).trans ?_
  exact two_request_outcomes k.firstLabel g (fun a => (k.secondLabel, k.secondQuery (assignment g a.2)))

theorem packed_outcomes (p : Program) (g : Bool) : p.observations g = p.key.outcomes g := by
  unfold Program.observations
  rw [packed_replay]
  exact key_outcomes p.key g

private theorem two_events {a b c d : Event}
    (h : FreeMonoid.of a * FreeMonoid.of b = FreeMonoid.of c * FreeMonoid.of d) :
    a = c ∧ b = d := by
  have words := congrArg FreeMonoid.toList h
  exact ⟨(List.cons.inj words).1, List.singleton_inj.mp (List.cons.inj words).2⟩

private theorem log_events {k l : Key} {g : Bool} {r₁ r₂ s₁ s₂ : Reply}
    (h : k.word g r₁ r₂ = l.word g s₁ s₂) :
    (⟨k.firstLabel, g, r₁.1, r₁.2⟩ : Event) = ⟨l.firstLabel, g, s₁.1, s₁.2⟩ ∧
    (⟨k.secondLabel, k.secondQuery (assignment g r₁.2), r₂.1, r₂.2⟩ : Event) =
      ⟨l.secondLabel, l.secondQuery (assignment g s₁.2), s₂.1, s₂.2⟩ :=
  two_events h

private theorem recover_key {k l : Key} (same : ∀ g, k.outcomes g = l.outcomes g) : k = l := by
  have detect (g r : Bool) :
      k.firstLabel = l.firstLabel ∧ k.secondLabel = l.secondLabel ∧
      k.secondQuery (assignment g r) = l.secondQuery (assignment g r) := by
    have hit : (.ok (atExit (answer false false)), k.word g (false, r) (false, false)) ∈ l.outcomes g :=
      (same g) ▸ (show _ ∈ k.outcomes g from ⟨((false, r), (false, false)), rfl⟩)
    rcases hit with ⟨⟨r₁, r₂⟩, sameLog⟩
    obtain ⟨firstEq, secondEq⟩ := log_events (congrArg Prod.snd sameLog).symm
    have eq : r = r₁.2 := congrArg Event.payload firstEq
    exact ⟨congrArg Event.label firstEq, congrArg Event.label secondEq,
      (congrArg Event.query secondEq).trans (congrArg (fun b => l.secondQuery (assignment g b)) eq.symm)⟩
  have exhaustive (env : Assignment 2) : assignment (env 1) (env 0) = env := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rw [Fin.eq_zero j]
    rfl
  have tables : k.secondQuery = l.secondQuery := funext fun env =>
    exhaustive env ▸ (detect (env 1) (env 0)).2.2
  have firstLabel := (detect false false).1
  have secondLabel := (detect false false).2.1
  cases k
  cases l
  simp only [Key.mk.injEq]
  exact ⟨firstLabel, secondLabel, tables⟩

theorem packed_eq_iff_key (p q : Program) : p.packed = q.packed ↔ p.key = q.key := by
  constructor
  · intro eq
    apply recover_key
    intro g
    rw [← packed_outcomes, ← packed_outcomes]
    unfold Program.observations
    rw [eq]
  · intro eq
    exact (packed_replay p).trans ((congrArg Key.packed eq).trans (packed_replay q).symm)

theorem observations_iff_packed_eq (p q : Program) :
    (∀ g, p.observations g = q.observations g) ↔ p.packed = q.packed := by
  constructor
  · intro same
    apply (packed_eq_iff_key p q).2
    exact recover_key (fun g => (packed_outcomes p g).symm.trans ((same g).trans (packed_outcomes q g)))
  · intro eq g
    unfold Program.observations
    rw [eq]

theorem xor_quote_replay : Example.xor.packed = Example.xorQuote.packed := by
  apply (packed_eq_iff_key _ _).2
  have rows : Example.xor.key.secondQuery = Example.xorQuote.key.secondQuery :=
    (funext (Expr.quote_eval 2 Example.xor.key.secondQuery)).symm
  exact congrArg (Key.mk true false) rows

theorem second_query_witness :
    Example.observation true ∈ Example.xor.observations true ∧
    Example.observation false ∈ Example.replyOnly.observations true ∧
    Example.observation true ∉ Example.replyOnly.observations true := by
  rw [packed_outcomes, packed_outcomes]
  refine ⟨⟨((true, false), (true, false)), rfl⟩, ⟨((true, false), (true, false)), rfl⟩, ?_⟩
  rintro ⟨⟨r, s⟩, h⟩
  have word : Example.replyOnly.key.word true r s =
      Example.xor.key.word true (true, false) (true, false) := congrArg Prod.snd h
  obtain ⟨first, second⟩ := log_events word
  have payload : r.2 = false := congrArg Event.payload first
  have query : r.2 = true := congrArg Event.query second
  exact Bool.false_ne_true (payload.symm.trans query)

theorem second_query_ne : Example.xor.packed ≠ Example.replyOnly.packed := by
  intro eq
  have same := (observations_iff_packed_eq _ _).2 eq true
  exact second_query_witness.2.2 (same ▸ second_query_witness.1)

namespace TaggedContinuations

open Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag (firstBy firstBy_typed)

theorem packed_replay (p : ByReplyTag.Program) : p.packed = p.key.packed := by
  have step (guard : Bool) : E [U, Bit]
      (firstBy p.firstLabel guard (p.left.region guard) (p.right.region guard))
      (firstBy p.firstLabel guard (p.left.key.region guard) (p.right.key.region guard)) Exits :=
    .case (.op (constructorBit_value guard .unit).hasType)
      (replay_row p.left.label p.left.query guard) (replay_row p.right.label p.right.query guard)
  have eq : E [Bit] p.region p.key.region Exits := .case (.var (i := 0) rfl) (step false) (step true)
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
    (eq.lsubstPost p.typed p.key.typed (fun _ _ hi =>
      (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hi).hasType))

private def nextRequest (k : ByReplyTag.Key) (guard : Bool) (firstReply : Reply) : Bool × Bool :=
  let a := k.arm firstReply.1
  (a.label, a.query guard firstReply.2)

private theorem key_run (k : ByReplyTag.Key) (g : Bool) :
    (denote.map k.packed).of (bit g) =
      (request k.firstLabel (bit g) >>= fun firstReply =>
        let next := nextRequest k g (replyFields firstReply)
        request next.1 (bit next.2) >>= fun secondReply => pure (atExit secondReply)) := by
  refine (run_packed k.typed g).trans ?_
  let arm (b : Bool) := firstBy_typed k.firstLabel b (k.left.typed b) (k.right.typed b)
  have execute (b : Bool) : runAt (arm b) ((PUnit.unit, bit b), PUnit.unit) =
      (request k.firstLabel (bit b) >>= fun firstReply =>
        let next := nextRequest k b (replyFields firstReply)
        request next.1 (bit next.2) >>= fun secondReply => pure (atExit secondReply)) := by
    refine (request_case_run k.firstLabel b (k.left.typed b) (k.right.typed b)
      ((PUnit.unit, bit b), PUnit.unit)).trans ?_
    congr 1
    funext a
    cases a
    · exact row_run k.left.label (k.left.query b) _ _
    · exact row_run k.right.label (k.right.query b) _ _
  refine (test_run (Γ := []) (arm false) (arm true) PUnit.unit g).trans ?_
  cases g <;> exact execute _

theorem packed_outcomes (p : ByReplyTag.Program) (g : Bool) :
    p.observations g = p.key.outcomes g := by
  unfold ByReplyTag.Program.observations
  rw [packed_replay]
  refine (congrArg (Tagged.outcomes (A := value (packedExitType Exits))) (key_run p.key g)).trans ?_
  exact two_request_outcomes p.firstLabel g (nextRequest p.key g)

private theorem key_history_iff (k l : ByReplyTag.Key) (g : Bool) (r s : Reply) :
    k.observe g r s ∈ l.outcomes g ↔
      k.firstLabel = l.firstLabel ∧ (k.arm r.1).label = (l.arm r.1).label ∧
        (k.arm r.1).query g r.2 = (l.arm r.1).query g r.2 := by
  constructor
  · rintro ⟨⟨r', s'⟩, same⟩
    have sameWord : (l.observe g r' s').2 = (k.observe g r s).2 := congrArg Prod.snd same
    obtain ⟨first, second⟩ := two_events sameWord.symm
    have history : r = r' := Prod.ext (congrArg Event.right first) (congrArg Event.payload first)
    subst r'
    exact ⟨congrArg Event.label first, congrArg Event.label second, congrArg Event.query second⟩
  · rintro ⟨first, label, query⟩
    refine ⟨(r, s), ?_⟩
    simp only [ByReplyTag.Key.observe, ByReplyTag.Key.firstEvent, ByReplyTag.Key.secondEvent, first, label, query]

theorem observed_history_iff (p q : ByReplyTag.Program) (g : Bool) (r s : Reply) :
    p.key.observe g r s ∈ q.observations g ↔
      p.key.firstLabel = q.key.firstLabel ∧ (p.key.arm r.1).label = (q.key.arm r.1).label ∧
        (p.key.arm r.1).query g r.2 = (q.key.arm r.1).query g r.2 :=
  by rw [packed_outcomes]; exact key_history_iff p.key q.key g r s

private theorem eq_of_rows {k l : ByReplyTag.Key}
    (row : ∀ tag g payload, k.firstLabel = l.firstLabel ∧ (k.arm tag).label = (l.arm tag).label ∧
      (k.arm tag).query g payload = (l.arm tag).query g payload) : k = l := by
  have armEq (tag : Bool) : k.arm tag = l.arm tag := by
    have label := (row tag false false).2.1
    have table := funext fun g => funext fun payload => (row tag g payload).2.2
    cases lk : k.arm tag
    cases ll : l.arm tag
    simp only [lk, ll, ByReplyTag.ArmKey.mk.injEq] at *
    exact ⟨label, table⟩
  have first := (row false false false).1
  have left : k.left = l.left := armEq false
  have right : k.right = l.right := armEq true
  cases k
  cases l
  simp only [ByReplyTag.Key.mk.injEq]
  exact ⟨first, left, right⟩

private theorem recover_key {k l : ByReplyTag.Key} (same : ∀ g, k.outcomes g = l.outcomes g) : k = l := by
  apply eq_of_rows
  intro tag g payload
  let r : Reply := (tag, payload)
  let s : Reply := (false, false)
  have hit : k.observe g r s ∈ k.outcomes g := ⟨(r, s), rfl⟩
  exact (key_history_iff k l g r s).mp (same g ▸ hit)

theorem packed_eq_iff_key (p q : ByReplyTag.Program) : p.packed = q.packed ↔ p.key = q.key := by
  constructor
  · intro eq
    apply recover_key
    intro g
    rw [← packed_outcomes, ← packed_outcomes]
    unfold ByReplyTag.Program.observations
    rw [eq]
  · intro eq
    exact (packed_replay p).trans ((congrArg ByReplyTag.Key.packed eq).trans (packed_replay q).symm)

theorem observations_iff_packed_eq (p q : ByReplyTag.Program) :
    (∀ g, p.observations g = q.observations g) ↔ p.packed = q.packed := by
  constructor
  · intro same
    apply (packed_eq_iff_key p q).2
    exact recover_key (fun g => (packed_outcomes p g).symm.trans ((same g).trans (packed_outcomes q g)))
  · intro same g
    unfold ByReplyTag.Program.observations
    rw [same]

private theorem agreesAt_iff (k l : ByReplyTag.Key) (g : Bool) (r : Reply) :
    k.agreesAt l g r = true ↔
      k.firstLabel = l.firstLabel ∧ (k.arm r.1).label = (l.arm r.1).label ∧
        (k.arm r.1).query g r.2 = (l.arm r.1).query g r.2 := by
  simp [ByReplyTag.Key.agreesAt, Bool.and_eq_true, and_assoc]

theorem history_check_iff (p q : ByReplyTag.Program) (g : Bool) (r s : Reply) :
    p.key.agreesAt q.key g r = true ↔ p.key.observe g r s ∈ q.observations g :=
  (agreesAt_iff p.key q.key g r).trans (observed_history_iff p q g r s).symm

theorem compare_iff (p q : ByReplyTag.Program) : p.compare q = true ↔ p.packed = q.packed := by
  rw [packed_eq_iff_key]
  constructor
  · intro result
    apply eq_of_rows
    intro tag g payload
    exact (agreesAt_iff p.key q.key g (tag, payload)).mp ((of_decide_eq_true result) tag g payload)
  · intro same
    apply decide_eq_true
    intro tag g payload
    exact (agreesAt_iff p.key q.key g (tag, payload)).mpr (same ▸ ⟨rfl, rfl, rfl⟩)

theorem policy_in_observations (p : ByReplyTag.Program) (policy : ByReplyTag.Policy) (g : Bool) :
    p.key.runPolicy policy g ∈ p.observations g := by
  rw [packed_outcomes]
  exact ⟨p.key.policyReplies policy g, rfl⟩

open ByReplyTag.Example (reference changed keepLeft)

theorem changed_row (tag g payload : Bool) :
    (reference.key.arm tag).query g payload ≠ (changed.key.arm tag).query g payload ↔
      tag = true ∧ g = true ∧ payload = false := by
  cases tag <;> cases g <;> cases payload <;> decide

theorem branch_witness :
    reference.key.observe true (true, false) (true, false) ∈ reference.observations true ∧
    reference.key.observe true (true, false) (true, false) ∉ changed.observations true ∧
    reference.key.observe true (false, false) (true, false) ∈ changed.observations true := by
  refine ⟨(observed_history_iff _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro h
    have query := ((observed_history_iff _ _ _ _ _).mp h).2.2
    exact ((changed_row true true false).mpr ⟨rfl, rfl, rfl⟩) query
  · exact (observed_history_iff _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

theorem branch_ne : reference.packed ≠ changed.packed := by
  intro h
  have same : reference.observations true = changed.observations true := by
    unfold ByReplyTag.Program.observations
    rw [h]
  exact branch_witness.2.1 (same ▸ branch_witness.1)

theorem checker_regression :
    reference.key.agreesAt changed.key true (false, false) = true ∧
    reference.key.agreesAt changed.key true (true, false) = false ∧
    reference.compare changed = false := by decide

theorem shared_policy_agrees (g : Bool) :
    reference.key.runPolicy keepLeft g = changed.key.runPolicy keepLeft g := rfl

end TaggedContinuations
end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TwoBitQueries
