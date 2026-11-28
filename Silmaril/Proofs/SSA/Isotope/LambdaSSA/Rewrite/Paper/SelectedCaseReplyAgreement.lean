module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Selected.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms

/-! # The selected fold at the witnessed payload separator's coordinates -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext caseWithContext_of pair_of)
open Silmaril.Isotope.LetIter.Semantics.Categorical (case_postcomp)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply (Trace Log Outcome Event prepend)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
  (Bit Answer Position signature Op model modelCoherent)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types
local notation "PJ" => Paper.WithProjectionReturnsAndUnitEta.denoteArrow
local notation "pack" => Paper.WithProjectionReturnsAndUnitEta.ExitPacking.packArrow

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

noncomputable local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel J M signature.Instr :=
  Kleisli.instructions model

local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

private abbrev emit (b : Bool) : Trace PUnit :=
  Tagged.ofOutcomes {(.ok PUnit.unit, FreeMonoid.of (Event.emit b))}

private abbrev ask (request : Bool) : Trace (value Answer) :=
  Tagged.ofOutcomes (Set.range fun reply : Bool × Bool =>
    (.ok (Reply.Payload.answer reply.1 reply.2), Reply.Payload.replyLog request reply.1 reply.2))

private theorem packed_injection {L : List (Ty Empty)} (i : Nat) {A : Ty Empty}
    (hi : At L i A) (x : value A) :
    (labelInject M i hi ≫ packLabel M L) x = Reply.Exits.packAt L i hi x := by
  have coordinate := ConcreteCategory.congr_hom (labelInject_packLabel M hi) x
  refine coordinate.trans ?_
  clear coordinate
  induction L generalizing i with
  | nil => cases i <;> contradiction
  | cons B L ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      simp only [packedLabelInject, Reply.Exits.packAt, eqToHom_refl, Category.id_comp]
      exact ConcreteCategory.congr_hom
        (Types.binaryCoproductIso_inl_comp_hom (value A) (value (packedExitType L))) x
    | succ i =>
      simp only [packedLabelInject, Reply.Exits.packAt]
      change (coprod.inr ≫ (Types.binaryCoproductIso (value B) (value (packedExitType L))).hom)
        (packedLabelInject M i hi x) = _
      rw [Types.binaryCoproductIso_inr_comp_hom, ih i hi]
      rfl

private theorem packed_position {L : List (Ty Empty)} (pos : Position L) (b : Bool) :
    (labelInject M pos.1 pos.typed ≫ packLabel M L) (Reply.Payload.bit b) =
      (pos.result b).packed := by
  rw [packed_injection]
  have castPack {A B : Ty Empty} (e : A = B) {i : Nat} (h : At L i A) (v : value B) :
      Reply.Exits.packAt L i (e ▸ h) v = Reply.Exits.packAt L i h (e.symm ▸ v) := by
    cases e
    rfl
  exact castPack pos.2 (labelAt_get L pos.1) (Reply.Payload.bit b)

private theorem emitPrefix_of {X D : Ty Empty} (bits : List Bool) (body : Term signature.Instr X D)
    (x : value X) :
    ((emitPrefix bits body).targetArrow J M).of x =
      bits.foldr (fun b next => emit b >>= fun _ => next) ((body.targetArrow J M).of x) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [emitPrefix, Term.targetArrow, orderedPair_eq_pair, Category.assoc,
      Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
    rw [pair_of (m := Trace)]
    simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
    change Bind.bind (m := Trace) (Bind.bind (m := Trace)
        (Bind.bind (m := Trace) (pure PUnit.unit) (fun _ => emit b))
        (fun u => Bind.bind (m := Trace) (((emitPrefix bs body).targetArrow J M).of x)
          (fun z => pure (u, z))))
      (fun p => Bind.bind (m := Trace) (pure p) (fun z => pure z.2)) = _
    simp only [pure_bind, bind_assoc, bind_pure, List.foldr, ih]

private theorem observe_bind {S A B : Type} (answer : S → A) (log : S → Log) (k : A → Trace B) :
    ((Tagged.ofOutcomes (Set.range fun s => (.ok (answer s), log s)) : Trace A) >>= k).outcomes =
      ⋃ s, (fun z : Outcome B => (z.1, log s * z.2)) '' (k (answer s)).outcomes := by
  ext z
  obtain ⟨result, word⟩ := z
  rw [Tagged.mem_bind, Set.mem_iUnion]
  constructor
  · rintro (⟨fault, _, ⟨s, hs⟩⟩ | ⟨a, u, v, ⟨s, hs⟩, hk, hw⟩)
    · cases (congrArg Prod.fst hs : Except.ok (answer s) = Except.error fault)
    · cases (Except.ok.inj (congrArg Prod.fst hs))
      cases (congrArg Prod.snd hs)
      exact ⟨s, (result, v), hk, congrArg (fun w => (result, w)) hw⟩
  · rintro ⟨s, ⟨⟨r, v⟩, hk, eq⟩⟩
    cases eq
    exact Or.inr ⟨answer s, log s, v, ⟨s, rfl⟩, hk, rfl⟩

private theorem emit_outcomes {A : Type} (bit : Bool) (next : Trace A) :
    (emit bit >>= fun _ => next).outcomes = prepend (.emit bit) '' next.outcomes := by
  simpa only [Set.range_const, Set.iUnion_const, prepend] using
    observe_bind (fun _ : Unit => (PUnit.unit : PUnit)) (fun _ => FreeMonoid.of (Event.emit bit)) (fun _ => next)

private theorem boolPair_union {A : Type} (f : Bool × Bool → Set A) :
    (⋃ r, f r) = (f (false, false) ∪ f (false, true)) ∪ (f (true, false) ∪ f (true, true)) := by
  rw [Set.iUnion_prod']
  change (⨆ i, ⨆ j, f (i, j)) = (f (false, false) ⊔ f (false, true)) ⊔ (f (true, false) ⊔ f (true, true))
  simp only [iSup_bool_eq, sup_comm]

private noncomputable abbrev runPacked {X : Ty Empty} {L : List (Ty Empty)} (t : CaseTree signature.Instr X L)
    (x : value X) : Trace (value (packedExitType L)) :=
  (t.targetArrow J M ≫ (J).map (packLabel M L)).of x

private theorem prefix_bind {A B : Type} (bits : List Bool) (start : Trace A) (finish : A → Trace B) :
    (bits.foldr (fun b next => emit b >>= fun _ => next) start >>= finish) =
      bits.foldr (fun b next => emit b >>= fun _ => next) (start >>= finish) := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr, bind_assoc, ih]

private theorem packedLeaf_of {X : Ty Empty} {L : List (Ty Empty)} (bits : List Bool) (pos : Position L)
    (body : Term signature.Instr X Bit) (x : value X) (b : Bool)
    (hb : (body.targetArrow J M).of x = (pure (Reply.Payload.bit b) : Trace (value Bit))) :
    runPacked (.exit pos.1 pos.typed (.returned (emitPrefix bits body))) x =
      bits.foldr (fun bit next => emit bit >>= fun _ => next) (pure ((pos.result b).packed)) := by
  simp only [runPacked, CaseTree.targetArrow, Program.targetArrow, Category.assoc,
    ← (J).map_comp, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Trace) (((emitPrefix bits body).targetArrow J M).of x)
    (fun v => pure ((labelInject M pos.1 pos.typed ≫ packLabel M L) v)) = _
  rw [emitPrefix_of, hb, prefix_bind]
  simp only [pure_bind, packed_position]
  rfl

private theorem ask_of {X : Ty Empty} (request : Bool) (x : value X) :
    ((Term.call (X := X) (show signature.Instr from Op.ask request) .unit).targetArrow J M).of x =
      ask request := by
  simp only [Term.targetArrow, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Trace) (pure PUnit.unit) (fun _ => ask request) = _
  rw [pure_bind]

private theorem emittingDiscriminator_of {X A B : Ty Empty} (bits : List Bool)
    (test : Term signature.Instr X (coprod A B)) (x : value X) :
    ((emitPrefix bits test).targetArrow J M ≫
      (J).map ((M).coprodIso A B).hom).of x =
      (bits.foldr (fun b next => emit b >>= fun _ => next) ((test.targetArrow J M).of x) >>=
        fun s => pure (((M).coprodIso A B).hom s)) := by
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  simp only [Bind.kleisliRight]
  erw [emitPrefix_of]
  rfl

private theorem packedArm_of {X A : Ty Empty} {L : List (Ty Empty)}
    (t : CaseTree signature.Instr (product X A) L) (x : value X) (b : value A) :
    ((((J).map ((M).productIso X A).inv ≫ t.targetArrow J M) ≫
        (J).map (packLabel M L)).of (x, b)) = runPacked t (x, b) := by
  simp only [runPacked, Category.assoc, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Trace) (pure (x, b)) _ = _
  rw [pure_bind]
  rfl

private theorem packedCase_of {X A B : Ty Empty} {L : List (Ty Empty)} (bits : List Bool)
    (test : Term signature.Instr X (coprod A B))
    (l : CaseTree signature.Instr (product X A) L)
    (r : CaseTree signature.Instr (product X B) L) (x : value X) :
    runPacked (.case A B (emitPrefix bits test) l r) x =
      bits.foldr (fun bit next => emit bit >>= fun _ => next)
        ((test.targetArrow J M).of x >>= fun | .inl a => runPacked l (x, a) | .inr b => runPacked r (x, b)) := by
  simp only [runPacked, CaseTree.targetArrow]
  rw [case_postcomp J, caseWithContext_of (m := Trace)]
  simp only [Bind.kleisliRight]
  erw [emittingDiscriminator_of]
  rw [bind_assoc, prefix_bind]
  have coordinate (s : value (coprod A B)) :
      (Types.binaryCoproductIso ((M).obj A) ((M).obj B)).hom (((M).coprodIso A B).hom s) = s :=
    ConcreteCategory.congr_hom (Types.binaryCoproductIso (value A) (value B)).inv_hom_id s
  simp only [pure_bind, coordinate]
  congr 1
  congr 1
  funext reply
  cases reply with
  | inl a => exact packedArm_of l x a
  | inr b => exact packedArm_of r x b

private theorem packedBitCase_of {X : Ty Empty} {L : List (Ty Empty)} (bits : List Bool)
    (test : Term signature.Instr X Bit) (l r : CaseTree signature.Instr (product X unit) L)
    (x : value X) (b : Bool) (h : (test.targetArrow J M).of x = (pure (Reply.Payload.bit b) : Trace (value Bit))) :
    runPacked (.case unit unit (emitPrefix bits test) l r) x =
      bits.foldr (fun bit next => emit bit >>= fun _ => next)
        (runPacked (if b then r else l) (x, PUnit.unit)) := by
  rw [packedCase_of]
  erw [h]
  rw [pure_bind]
  cases b <;> rfl

private theorem retainSlot_of {X A : Ty Empty} (slot : Term signature.Instr X Bit) (x : value X) (a : value A) :
    ((retainSlot (A := A) slot).targetArrow J M).of (x, a) = (slot.targetArrow J M).of x := by
  simp only [retainSlot, Term.targetArrow, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Trace) (pure x) (fun y => (slot.targetArrow J M).of y) = _
  rw [pure_bind]

private theorem packedRequest_of {X : Ty Empty} {L : List (Ty Empty)} (bits : List Bool)
    (request : Bool) (l r : CaseTree signature.Instr (product X Bit) L) (x : value X) :
    runPacked (.case Bit Bit (emitPrefix bits (.call (show signature.Instr from Op.ask request) .unit)) l r) x =
      bits.foldr (fun bit next => emit bit >>= fun _ => next)
        (ask request >>= fun | .inl a => runPacked l (x, a) | .inr b => runPacked r (x, b)) := by
  rw [packedCase_of]
  erw [ask_of request x]
  congr 1
  congr 1
  funext reply
  cases reply <;> rfl

private theorem bitTag_of (b : Bool) :
    ((bitTag b).valueMap M) PUnit.unit = Reply.Payload.bit b := by
  cases b
  · exact ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value unit) (value unit)) PUnit.unit
  · exact ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_hom (value unit) (value unit)) PUnit.unit

private theorem packedLiteral_of {X : Ty Empty} {L : List (Ty Empty)} (bits : List Bool)
    (pos : Position L) (x : value X) (b : Bool) :
    runPacked (.taggedExit pos.1 pos.typed (bitTag b) (emitPrefix bits (.unit : Term signature.Instr X unit))) x =
      bits.foldr (fun bit next => emit bit >>= fun _ => next) (pure ((pos.result b).packed)) := by
  simp only [runPacked, CaseTree.targetArrow, Category.assoc, ← (J).map_comp,
    Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Trace) (((emitPrefix bits (.unit : Term signature.Instr X unit)).targetArrow J M).of x)
    (fun v => pure ((labelInject M pos.1 pos.typed ≫ packLabel M L) (((bitTag b).valueMap M) v))) = _
  rw [emitPrefix_of, prefix_bind]
  rw [show ((Term.unit (Φ := signature.Instr) (X := X)).targetArrow J M).of x =
    (pure PUnit.unit : Trace (value unit)) from rfl]
  simp only [pure_bind, bitTag_of, packed_position]
  rfl

private theorem selectTerminal_of {L : List (Ty Empty)} (pos : Position L)
    {n : Nat} (e : Reply.Payload.Finite.Expr n) {X : Ty Empty}
    (slots : Fin n → Term signature.Instr X Bit) (bits : List Bool) (x : value X)
    (env : Reply.Payload.Finite.Assignment n)
    (hslots : ∀ i, ((slots i).targetArrow J M).of x = (pure (Reply.Payload.bit (env i)) : Trace (value Bit))) :
    runPacked (selectTerminal pos e slots bits) x =
      bits.foldr (fun bit next => emit bit >>= fun _ => next) (pure ((pos.result (e.eval env)).packed)) := by
  induction e generalizing X bits with
  | literal b => exact packedLiteral_of bits pos x b
  | read i => exact packedLeaf_of bits pos (slots i) x (env i) (hslots i)
  | split low high ihl ihr =>
    rw [selectTerminal, packedBitCase_of _ _ _ _ _ _ (hslots 0)]
    have older (i : Fin _) :
        ((retainSlot (A := unit) (slots i.succ)).targetArrow J M).of (x, PUnit.unit) =
          (pure (Reply.Payload.bit (env.tail i)) : Trace (value Bit)) :=
      (retainSlot_of (A := unit) (slots i.succ) x PUnit.unit).trans (hslots i.succ)
    cases h : env 0
    · simp only [h, Reply.Payload.Finite.Expr.eval, Bool.false_eq_true, ↓reduceIte]
      rw [ihl (X := product X unit) _ [] (x, PUnit.unit) env.tail older]
      rfl
    · simp only [h, Reply.Payload.Finite.Expr.eval, ↓reduceIte]
      rw [ihr (X := product X unit) _ [] (x, PUnit.unit) env.tail older]
      rfl

private theorem prepend_outcomes {D R : Type} (bits : List Bool) (start : Trace D)
    (paths : Reply.Normal R) (success : R → D) (h : start.outcomes = paths.outcomesWith success) :
    (bits.foldr (fun b next => emit b >>= fun _ => next) start).outcomes =
      (bits.foldr Reply.Normal.emit paths).outcomesWith success := by
  induction bits with
  | nil => exact h
  | cons b bs ih =>
    simp only [List.foldr, Reply.Normal.outcomesWith, emit_outcomes, ih]

private theorem request_outcomes {D R : Type} (req : Bool) (l r : value Bit → Trace D)
    (left right : Bool → Reply.Normal R) (success : R → D)
    (hl : ∀ b, (l (Reply.Payload.bit b)).outcomes = (left b).outcomesWith success)
    (hr : ∀ b, (r (Reply.Payload.bit b)).outcomes = (right b).outcomesWith success) :
    (ask req >>= fun | .inl a => l a | .inr b => r b).outcomes =
      (Reply.Payload.requestTree req left right).outcomesWith success := by
  rw [observe_bind, boolPair_union]
  simp only [Reply.Payload.answer, Bool.false_eq_true, ↓reduceIte, hl, hr,
    Reply.Payload.requestTree, Reply.Normal.outcomesWith, Set.image_union, Set.image_image,
    prepend, Reply.Payload.replyLog, mul_assoc]

private theorem prefix_outcomes {D R : Type} (bits : List Bool) (success : R → D) (r : R) :
    (bits.foldr (fun b next => emit b >>= fun _ => next) (pure (success r))).outcomes =
      (bits.foldr Reply.Normal.emit (.ret r)).outcomesWith success :=
  prepend_outcomes bits _ _ success rfl

private theorem leaf_observe {L : List (Ty Empty)} (a : Reply.Payload.Arm L)
    (direct : a.result = .payload) (b : Bool) :
    (runPacked (payloadLeaf a.emits a.position) (PUnit.unit, Reply.Payload.bit b)).outcomes =
      (a.normal.traceTree b).outcomesWith Reply.Exits.Exit.packed := by
  rw [payloadLeaf, packedLeaf_of _ _ (.snd unit Bit) _ b rfl,
    prefix_outcomes a.emits Reply.Exits.Exit.packed (a.position.result b)]
  cases b <;> simp only [Reply.Payload.ArmNormal.traceTree, Reply.Payload.ArmNormal.result,
    Reply.Payload.Arm.normal, direct, Reply.Payload.Expr.evaluate, Bool.false_eq_true, ↓reduceIte]

/-- The one-request presentation uses the same packed case and leaf computations. -/
theorem packed_outcomes (H : Ty Empty) (L : List (Ty Empty)) (p : DirectProgram (H :: L)) :
    ((PJ J M (fun _ _ => ⟨rfl, rfl⟩) (pack p.selected.elaborate.property)).of PUnit.unit).outcomes =
      Reply.Payload.programOutcomes H L p.val := by
  rw [p.selected.denote_packArrow J M (fun _ _ => ⟨rfl, rfl⟩), Reply.Payload.programOutcomes_eq]
  have h := packedRequest_of [] p.val.request (payloadLeaf p.val.left.emits p.val.left.position)
    (payloadLeaf p.val.right.emits p.val.right.position) PUnit.unit
  change runPacked p.selected PUnit.unit = _ at h
  change (runPacked p.selected PUnit.unit).outcomes = _
  rw [h]
  exact request_outcomes p.val.request _ _ p.val.left.normal.traceTree p.val.right.normal.traceTree
    Reply.Exits.Exit.packed (leaf_observe _ p.property.1) (leaf_observe _ p.property.2)

private theorem bindReply_of {X : Ty Empty} {n : Nat} (slots : Fin n → Term signature.Instr X Bit)
    (x : value X) (env : Reply.Payload.Finite.Assignment n)
    (hslots : ∀ i, ((slots i).targetArrow J M).of x = (pure (Reply.Payload.bit (env i)) : Trace (value Bit)))
    (b : Bool) (i : Fin (n + 1)) :
    ((bindReply slots i).targetArrow J M).of (x, Reply.Payload.bit b) =
      (pure (Reply.Payload.bit (env.push b i)) : Trace (value Bit)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [bindReply, Reply.Payload.Finite.Assignment.push, Fin.cases_zero]
    rfl
  · simp only [bindReply, Reply.Payload.Finite.Assignment.push, Fin.cases_succ, retainSlot_of]
    exact hslots j

private theorem emit_traceTree {L : List (Ty Empty)} {n : Nat} (bits : List Bool)
    (t : Reply.Payload.Finite.Tree L n) (env : Reply.Payload.Finite.Assignment n) :
    (bits.foldr Reply.Payload.Finite.Tree.emit t).normal.traceTree env =
      bits.foldr Reply.Normal.emit (t.normal.traceTree env) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldr, Reply.Payload.Finite.Tree.normal, Reply.Payload.Finite.Normal.traceTree, ih]

private theorem selectedRequest_observe {X : Ty Empty} {L : List (Ty Empty)} {n : Nat} (bits : List Bool)
    (req : Bool) (l r : CaseTree signature.Instr (product X Bit) L) (x : value X)
    (left right : Reply.Payload.Finite.Normal L (n + 1)) (env : Reply.Payload.Finite.Assignment n)
    (hl : ∀ b, (runPacked l (x, Reply.Payload.bit b)).outcomes = left.outcomes (env.push b))
    (hr : ∀ b, (runPacked r (x, Reply.Payload.bit b)).outcomes = right.outcomes (env.push b)) :
    (runPacked (selectRequest bits req l r) x).outcomes =
      (bits.foldr Reply.Normal.emit ((Reply.Payload.Finite.Normal.request req left right).traceTree env)).outcomesWith
        Reply.Exits.Exit.packed := by
  rw [selectRequest, packedRequest_of]
  apply prepend_outcomes
  exact request_outcomes req _ _ _ _ Reply.Exits.Exit.packed hl hr

private theorem readTree_observe {L : List (Ty Empty)} {n : Nat}
    (p : ReadTree L n) {X : Ty Empty} (slots : Fin n → Term signature.Instr X Bit)
    (x : value X) (env : Reply.Payload.Finite.Assignment n)
    (hslots : ∀ i, ((slots i).targetArrow J M).of x = (pure (Reply.Payload.bit (env i)) : Trace (value Bit))) :
    (runPacked (p.selectedWith slots) x).outcomes = p.witnessed.normal.outcomes env := by
  induction p generalizing X with
  | ret bits pos i =>
    rw [ReadTree.selectedWith, selectTerminal_of pos (.read i) slots bits x env hslots,
      ReadTree.witnessed, Reply.Payload.Finite.Normal.outcomes, emit_traceTree]
    exact prefix_outcomes bits Reply.Exits.Exit.packed (pos.result (env i))
  | retExpr bits pos e =>
    rw [ReadTree.selectedWith, selectTerminal_of pos e slots bits x env hslots,
      ReadTree.witnessed, Reply.Payload.Finite.Normal.outcomes, emit_traceTree]
    exact prefix_outcomes bits Reply.Exits.Exit.packed (pos.result (e.eval env))
  | request bits req bound l r ihl ihr =>
    rw [ReadTree.selectedWith, ReadTree.witnessed, Reply.Payload.Finite.Normal.outcomes, emit_traceTree]
    exact selectedRequest_observe bits req _ _ x l.witnessed.normal r.witnessed.normal env
      (fun b => ihl (bindReply slots) (x, Reply.Payload.bit b) (env.push b) (bindReply_of slots x env hslots b))
      (fun b => ihr (bindReply slots) (x, Reply.Payload.bit b) (env.push b) (bindReply_of slots x env hslots b))
  | testRequest bits test low lowBound highBound fl fr tl tr ihfl ihfr ihtl ihtr =>
    rw [ReadTree.selectedWith, packedBitCase_of _ _ _ _ _ _ (hslots test),
      ReadTree.witnessed, Reply.Payload.Finite.Normal.outcomes, emit_traceTree]
    apply prepend_outcomes
    have remaining (i : Fin _) :
        ((retainSlot (A := unit) (slots (test.succAbove i))).targetArrow J M).of (x, PUnit.unit) =
          (pure (Reply.Payload.bit (env.without test i)) : Trace (value Bit)) :=
      (retainSlot_of (A := unit) (slots (test.succAbove i)) x PUnit.unit).trans (hslots (test.succAbove i))
    have nextSlot (b : Bool) := bindReply_of (X := product X unit) _ (x, PUnit.unit) (env.without test) remaining b
    cases h : env test
    · simp only [Reply.Payload.Finite.Tree.normal, Reply.Payload.Finite.Normal.traceTree, h, Bool.false_eq_true,
        ↓reduceIte]
      exact selectedRequest_observe (X := product X unit) [] low _ _ (x, PUnit.unit) fl.witnessed.normal fr.witnessed.normal
        (env.without test)
        (fun b => ihfl (X := product (product X unit) Bit) _ ((x, PUnit.unit), Reply.Payload.bit b) ((env.without test).push b) (nextSlot b))
        (fun b => ihfr (X := product (product X unit) Bit) _ ((x, PUnit.unit), Reply.Payload.bit b) ((env.without test).push b) (nextSlot b))
    · simp only [Reply.Payload.Finite.Tree.normal, Reply.Payload.Finite.Normal.traceTree, h, ↓reduceIte]
      exact selectedRequest_observe (X := product X unit) [] (!low) _ _ (x, PUnit.unit) tl.witnessed.normal tr.witnessed.normal
        (env.without test)
        (fun b => ihtl (X := product (product X unit) Bit) _ ((x, PUnit.unit), Reply.Payload.bit b) ((env.without test).push b) (nextSlot b))
        (fun b => ihtr (X := product (product X unit) Bit) _ ((x, PUnit.unit), Reply.Payload.bit b) ((env.without test).push b) (nextSlot b))

theorem replyInput_surjective (n : Nat) : Function.Surjective (replyInput n) := by
  induction n with
  | zero =>
    rintro ⟨⟩
    exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
    rintro ⟨x, b⟩
    obtain ⟨env, rfl⟩ := ih x
    rcases b with ⟨⟩ | ⟨⟩
    · exact ⟨env.push false, rfl⟩
    · exact ⟨env.push true, rfl⟩

private theorem readReply_input (n : Nat) (env : Reply.Payload.Finite.Assignment n) (i : Fin n) :
    ((readReply n i).targetArrow J M).of (replyInput n env) =
      (pure (Reply.Payload.bit (env i)) : Trace (value Bit)) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact (retainSlot_of (A := Bit) (readReply n j) (replyInput n env.tail) (Reply.Payload.bit (env 0))).trans
      (ih env.tail j)

theorem readTree_packed_assignment {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    (env : Reply.Payload.Finite.Assignment n) :
    ((PJ J M (fun _ _ => ⟨rfl, rfl⟩) (pack p.selected.elaborate.property)).of (replyInput n env)).outcomes =
      p.witnessed.normal.outcomes env := by
  rw [p.selected.denote_packArrow J M (fun _ _ => ⟨rfl, rfl⟩)]
  exact readTree_observe p (readReply n) (replyInput n env) env (readReply_input n env)

theorem readTree_packed_outcomes (H : Ty Empty) (L : List (Ty Empty)) (p : ReadTree (H :: L) 0) :
    ((PJ J M (fun _ _ => ⟨rfl, rfl⟩) (pack p.selected.elaborate.property)).of PUnit.unit).outcomes =
      Reply.Payload.Finite.programOutcomes H L p.witnessed := by
  rw [Reply.Payload.Finite.programOutcomes_eq]
  exact readTree_packed_assignment p Fin.elim0

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement
