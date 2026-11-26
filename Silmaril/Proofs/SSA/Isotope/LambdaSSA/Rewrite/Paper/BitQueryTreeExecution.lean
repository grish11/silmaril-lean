module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Replay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Soundness.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms

/-! # Exact ordered traces of selected finite request trees -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeExecution

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.Execution Paper.WithCaseBind.BitQuery.RequestTree
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open scoped MonoidalCategory

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types
local notation "U" => (Ty.unit : Ty Empty)

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

private theorem denote_congr {Γ : VCtx (Ty Empty)} {r s : Region signature.Instr}
    (eq : r = s) (hr : HasType Γ r Exits) (hs : HasType Γ s Exits) :
    denoteRegion J M hr = denoteRegion J M hs := by
  subst s
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem weaken_run {Γ : VCtx (Ty Empty)} {r : Region signature.Instr}
    (h : ValueBranches Γ r Exits) (x : ctxObj M Γ) :
    runAt (h.renameVars (Ren.wk Γ U)) (x, PUnit.unit) = runAt h x := by
  let hw := h.renameVars (Ren.wk Γ U)
  let u : Tm.HasType Γ (.unit : Tm signature.Instr) U := .unit
  obtain ⟨ht, den⟩ := RegionDenotes.substValue J M (denoteRegion_spec J M hw.hasType)
    (Denotes.unit : Denotes J M u ((J).map (SemiCartesianMonoidalCategory.toUnit _ ≫ (M).unitIso.inv)))
  have eq := (RegionDenotes.eq_denote J M den).trans (denote_congr (drop_weakening r .unit) ht h.hasType)
  unfold runAt
  rw [← eq]
  rw [Category.assoc]
  symm
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure (x, PUnit.unit)) (fun y => runAt hw y) =
    runAt hw (x, PUnit.unit)
  rw [pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem test_run {Γ : VCtx (Ty Empty)} {i : Nat} (hi : At Γ i Bit)
    {l r : Region signature.Instr} (hl : ValueBranches (U :: Γ) l Exits)
    (hr : ValueBranches (U :: Γ) r Exits) (x : ctxObj M Γ) (b : Bool)
    (read : (lookup M i hi) x = bit b) :
    runAt (.case (.var hi) hl hr) x =
      if b then runAt hr (x, PUnit.unit) else runAt hl (x, PUnit.unit) := by
  have h := case_run (Denotes.var («J» := Kleisli.J (m := Trace)) («M» := Kleisli.types) hi) hl hr x
  change runAt (.case (.var hi) hl hr) x =
    Bind.bind (m := Trace) (pure ((lookup M i hi) x)) _ at h
  erw [h, read, pure_bind]
  cases b <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem choose_run {n : Nat} (q : Expr n) {Γ : VCtx (Ty Empty)}
    (indices : Fin n → Nat) (typed : ∀ i, At Γ (indices i) Bit) (env : Assignment n) (x : ctxObj M Γ)
    (read : ∀ i, (lookup M (indices i) (typed i)) x = bit (env i))
    {l r : Region signature.Instr} (hl : ValueBranches Γ l Exits) (hr : ValueBranches Γ r Exits) :
    runAt (choose_typed q (slots := fun i => .var (indices i)) (fun i => .var (typed i)) hl hr) x =
      if q.eval env then runAt hr x else runAt hl x := by
  induction q generalizing Γ l r with
  | literal b => cases b <;> rfl
  | read i =>
    refine (test_run (typed i) (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U))
      x (env i) (read i)).trans ?_
    cases val : env i
    · simp only [Expr.eval, val, Bool.false_eq_true, ite_false]
      exact weaken_run hl x
    · simp only [Expr.eval, val, ite_true]
      exact weaken_run hr x
  | @split n lo hi ihl ihr =>
    let wl := hl.renameVars (Ren.wk Γ U)
    let wr := hr.renameVars (Ren.wk Γ U)
    let older := fun (i : Fin n) => (indices i.succ).succ
    have ht (i : Fin n) : At (U :: Γ) (older i) Bit := typed i.succ
    have hv (i : Fin n) : (lookup M (older i) (ht i)) (x, PUnit.unit) = bit (env.tail i) := read i.succ
    refine (test_run (typed 0)
      (choose_typed lo (slots := fun i => .var (older i)) (fun i => .var (ht i)) wl wr)
      (choose_typed hi (slots := fun i => .var (older i)) (fun i => .var (ht i)) wl wr)
      x (env 0) (read 0)).trans ?_
    cases branch : env 0
    · simp only [Expr.eval, branch, Bool.false_eq_true, ite_false]
      refine (ihl older ht env.tail (x, PUnit.unit) hv wl wr).trans ?_
      cases val : lo.eval env.tail
      · exact weaken_run hl x
      · exact weaken_run hr x
    · simp only [Expr.eval, branch, ite_true]
      refine (ihr older ht env.tail (x, PUnit.unit) hv wl wr).trans ?_
      cases val : hi.eval env.tail
      · exact weaken_run hl x
      · exact weaken_run hr x

set_option backward.isDefEq.respectTransparency false in
private theorem branch_run {Γ : VCtx (Ty Empty)} (x : ctxObj M Γ) {i : Nat} (hi : At Γ i Bit)
    (right : Bool) (b : Bool) (read : (lookup M i hi) x = bit b) :
    runAt (.br (exit_typed right) (.var hi)) x = pure (terminal right b) := by
  unfold runAt
  have d := RegionDenotes.eq_denote J M
    (RegionDenotes.br (h := exit_typed right)
      (Denotes.var («J» := Kleisli.J (m := Trace)) («M» := Kleisli.types) (Φ := signature.Instr) hi))
  erw [← d]
  have comp := (J).map_comp (labelInject M _ (exit_typed right)) (packLabel M Exits)
  erw [Category.assoc, ← comp, labelInject_packLabel, Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure ((lookup M i hi) x))
    (fun y => pure ((packedLabelInject M _ (exit_typed right)) y)) = _
  rw [read, pure_bind]
  apply congrArg (pure (f := Trace))
  cases right
  · simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Bool.false_eq_true, ite_false]
    exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom
      (value Bit) (value (packedExitType [Bit]))) (bit b)
  · simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Category.assoc, ite_true]
    have inner := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType []))) (bit b)
    have outer := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_hom (value Bit) (value (packedExitType [Bit])))
        (Sum.inl (bit b) : value (packedExitType [Bit]))
    change (coprod.inr ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType [Bit]))).hom)
      ((coprod.inl ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType []))).hom) (bit b)) = _
    rw [inner]
    exact outer

private theorem bind_matches {Γ : VCtx (Ty Empty)} {n : Nat} (slots : Slots Γ n) (x : ctxObj M Γ)
    (env : Assignment n) (hslots : ∀ i, (lookup M (slots.index i) (slots.typed i)) x = bit (env i))
    (b : Bool) (i : Fin (n + 1)) :
    (lookup M (slots.bind.index i) (slots.bind.typed i)) (x, bit b) = bit (env.push b i) := by
  refine Fin.cases rfl (fun j => ?_) i
  exact hslots j

set_option backward.isDefEq.respectTransparency false in
private theorem run_outcomes {n : Nat} (t : Tree n) {Γ : VCtx (Ty Empty)} (slots : Slots Γ n)
    (x : ctxObj M Γ) (env : Assignment n)
    (hslots : ∀ i, (lookup M (slots.index i) (slots.typed i)) x = bit (env i)) :
    (runAt (t.typed slots) x).outcomes = t.outcomes env := by
  induction t generalizing Γ with
  | ret right i =>
    change (runAt (.br (exit_typed right) (.var (slots.typed i))) x).outcomes = _
    rw [branch_run x (slots.typed i) right (env i) (hslots i)]
    rfl
  | ask label query l r ihl ihr =>
    let hl := l.typed slots.bind
    let hr := r.typed slots.bind
    let finish (z : value Answer) : Trace Result :=
      match z with
      | .inl b => runAt hl (x, b)
      | .inr b => runAt hr (x, b)
    have invoke : runAt ((Tree.ask label query l r).typed slots) x =
        (request label (bit (query.eval env)) >>= finish) := by
      refine (choose_run query slots.index slots.typed env x hslots
        (request_typed label false hl hr) (request_typed label true hl hr)).trans ?_
      cases val : query.eval env
      · exact request_case_run label false hl hr x
      · exact request_case_run label true hl hr x
    rw [invoke]
    apply Set.ext
    rintro ⟨result, word⟩
    rw [bind_request]
    have after (reply : Reply) :
        (finish (answer reply.1 reply.2)).outcomes =
          if reply.1 then r.outcomes (env.push reply.2) else l.outcomes (env.push reply.2) := by
      obtain ⟨tag, b⟩ := reply
      cases tag
      · exact ihl slots.bind (x, bit b) (env.push b) (bind_matches slots x env hslots b)
      · exact ihr slots.bind (x, bit b) (env.push b) (bind_matches slots x env hslots b)
    simp only [after, Tree.outcomes, Set.mem_ofPred_eq, event]

theorem packed_outcomes (t : Tree 1) (b : Bool) :
    t.observations b = t.outcomes (fun _ => b) := by
  unfold Tree.observations
  rw [packed_unguarded]
  rw [run_packed (t.typed inputSlots) b]
  exact run_outcomes t inputSlots (PUnit.unit, bit b) (fun _ => b) (fun _ => rfl)

private theorem word_head {a b : Event} {v w : Word}
    (h : FreeMonoid.of a * v = FreeMonoid.of b * w) : a = b ∧ v = w := by
  have eq := List.cons.inj (congrArg FreeMonoid.toList h)
  exact ⟨eq.1, congrArg FreeMonoid.ofList eq.2⟩

/-- Recover an actual ordered history before interpreting its next continuation. -/
private theorem outcome_with_head {n : Nat} (env : Assignment n) (label : Bool) (q : Expr n)
    (l r : Tree (n + 1)) (e : Event) (tail : Word) (result : Except Bool Result) :
    (result, FreeMonoid.of e * tail) ∈ (Tree.ask label q l r).outcomes env ↔
      e.label = label ∧ e.query = q.eval env ∧
        (result, tail) ∈ (if e.right then r.outcomes (env.push e.payload) else l.outcomes (env.push e.payload)) := by
  constructor
  · rintro ⟨reply, rest, hit, log⟩
    obtain ⟨headEq, restEq⟩ := word_head log
    have a : reply.1 = e.right := congrArg Event.right headEq
    have b : reply.2 = e.payload := congrArg Event.payload headEq
    refine ⟨(congrArg Event.label headEq).symm, (congrArg Event.query headEq).symm, ?_⟩
    rwa [a, b, restEq] at hit
  · rintro ⟨hl, hq, hit⟩
    refine ⟨(e.right, e.payload), tail, hit, ?_⟩
    have same : event label (q.eval env) (e.right, e.payload) = e := by
      cases e
      cases hl
      cases hq
      rfl
    rw [same]

theorem last_query_difference (input firstTag firstPayload secondTag secondPayload : Bool) :
    let env := Assignment.push (Assignment.push (fun _ : Fin 1 => input) firstPayload) secondPayload
    let askQuery := fun altered => if altered && firstTag && secondTag then Expr.literal false else Example.lastQuery
    (askQuery false).eval env ≠ (askQuery true).eval env ↔
      input = true ∧ firstTag = true ∧ firstPayload = true ∧ secondTag = true ∧ secondPayload = false := by
  cases input <;> cases firstTag <;> cases firstPayload <;> cases secondTag <;> cases secondPayload <;> decide

theorem three_request_witness :
    Example.observation true ∈ (Example.program false).observations true ∧
    Example.observation false ∈ (Example.program true).observations true ∧
    Example.observation true ∉ (Example.program true).observations true := by
  rw [packed_outcomes, packed_outcomes]
  constructor
  · exact ⟨(true, true), _, ⟨(true, false), _, ⟨(true, false), 1, rfl, rfl⟩, rfl⟩, rfl⟩
  · constructor
    · exact ⟨(true, true), _, ⟨(true, false), _, ⟨(true, false), 1, rfl, rfl⟩, rfl⟩, rfl⟩
    · intro hit
      have first := (outcome_with_head (fun _ => true) false (.read 0)
        (Example.second true false) (Example.second true true)
        (event false true (true, true)) _ _).mp hit
      have second := (outcome_with_head (Assignment.push (fun _ : Fin 1 => true) true) true
        (.read 0) (Example.third true true false) (Example.third true true true)
        (event true true (true, false)) _ _).mp first.2.2
      have last := (outcome_with_head
        ((Assignment.push (fun _ : Fin 1 => true) true).push false) false (.literal false)
        (.ret false 0) (.ret true 0) (event false true (true, false)) _ _).mp second.2.2
      cases last.2.1

theorem three_request_ne : (Example.program false).packed ≠ (Example.program true).packed := by
  intro h
  have e : (Example.program false).observations true = (Example.program true).observations true := by
    unfold Tree.observations
    rw [h]
  exact three_request_witness.2.2 (e ▸ three_request_witness.1)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeExecution
