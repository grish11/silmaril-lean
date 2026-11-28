module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumRecursiveSchedule
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Join.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Transport.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.OrderedPairs.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive

open Region (HasType ValueBranches)
open Region.Paper
open Region.Paper.WithComputedCallReturns
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.RetainedCase (boundCase)
open Region.Paper.UnaryReturn.Beta.Constructors (pairSequence)
open Region.CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Morphism.CaseSSA (erase erase_hasType)
open LetCase.LocallyNameless (Derivation)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] (pe : ε)

private theorem ofOrdered {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {r s : Region Φ}
    (h : OrderedPairs.Eqv pe Γ r s L) : Continuation.Eqv pe Γ r s L :=
  Continuation.ofSums (SumBind.ofProducts (ProductBind.ofPairs h))

private theorem ofCalls {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {r s : Region Φ}
    (h : ConstructorJoin.Eqv pe Γ r s L) : Continuation.Eqv pe Γ r s L :=
  ofOrdered pe (OrderedPairs.ofCalls h)

private theorem unary {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {r s : Region Φ}
    (e : UnaryReturn.Step Γ r s L) : Continuation.Eqv pe Γ r s L :=
  ofCalls pe (.extra e.typed.1 e.typed.2 (.inl (.inl (.inr (.inl e)))))

private theorem returns_one {Γ : VCtx (Ty α)} {D : Ty α} {a : Tm Φ} (ha : Tm.HasType Γ a D) :
    Continuation.Eqv pe Γ (returnRegion a) (returnOnce a) [D] :=
  ofCalls pe (UnaryReturn.returnRegion_eq_returnOnce (fun e => .inl (.inl (.inr (.inl e)))) ha)

private theorem append_eq {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {A : Ty α}
    {p p' q q' : Region Φ} (hp : ValueBranches Γ p [A]) (hp' : ValueBranches Γ p' [A])
    (e : Continuation.Eqv pe Γ p p' [A]) (k : Continuation.Eqv pe (A :: Γ) q q' L) :
    Continuation.Eqv pe Γ (p.lsubst (fun _ => q)) (p'.lsubst (fun _ => q')) L :=
  (Extension.Eqv.lsubstCongr hp (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ k)).trans
    (.lsubstPost e hp hp' (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ k.typed.2))

private theorem append_return (a : Tm Φ) (q : Region Φ) :
    (returnOnce a).lsubst (fun _ => q) = .let₁ a q :=
  Region.lsubst_bindBranchArguments_br 0 a _

private theorem pure_leaf {Γ : VCtx (Ty α)} {A : Ty α} {a : Tm Φ}
    (value : Tm.BranchValue Γ a A) :
    ∃ s paths, Schedule Γ s [A] paths ∧ Continuation.Eqv pe Γ (returnOnce a) s [A] :=
  ⟨_, _, .ret (i := 0) rfl value, .paper (.cfgEta (.native (.letValue value (.br (ℓ := 0) rfl (.var rfl)))))⟩

private theorem replay_let {Γ : VCtx (Ty α)} {A D : Ty α} {a b : Tm Φ} {p q : Region Φ}
    {before after : List (List Φ × Nat)}
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b D)
    (hp : Schedule Γ p [A] before) (hq : Schedule (A :: Γ) q [D] after)
    (ep : Continuation.Eqv pe Γ (returnOnce a) p [A])
    (eq : Continuation.Eqv pe (A :: Γ) (returnOnce b) q [D]) :
    ∃ s paths, Schedule Γ s [D] paths ∧ Continuation.Eqv pe Γ (returnOnce (.let₁ a b)) s [D] := by
  obtain ⟨s, paths, scheduled, _, done⟩ := splice_schedule_proof (pe := pe) hp hq rfl
  have composed := append_eq pe (UnaryReturn.returnOnce_valueBranches ha) hp.valueBranches ep eq
  rw [append_return] at composed
  exact ⟨s, paths, scheduled, (unary pe (.fuse ha hb)).symm.trans (composed.trans done)⟩

private theorem replay_let₂ {Γ : VCtx (Ty α)} {A B D : Ty α} {a b : Tm Φ} {p q : Region Φ}
    {before after : List (List Φ × Nat)}
    (ha : Tm.HasType Γ a (product A B)) (hb : Tm.HasType (B :: A :: Γ) b D)
    (hp : Schedule Γ p [product A B] before) (hq : Schedule (B :: A :: Γ) q [D] after)
    (ep : Continuation.Eqv pe Γ (returnOnce a) p [product A B])
    (eq : Continuation.Eqv pe (B :: A :: Γ) (returnOnce b) q [D]) :
    ∃ s paths, Schedule Γ s [D] paths ∧ Continuation.Eqv pe Γ (returnOnce (.let₂ a b)) s [D] := by
  have unpack : Schedule (product A B :: Γ) (ProductBind.unpack q) [D] after :=
    .unpackVar (slot := 0) rfl (Continuation.rename_schedule hq (((Ren.wk Γ (product A B)).lift A).lift B))
  have replay := ProductBind.bind_replay_with (seed := Continuation.Seed pe)
    (fun e => .inl (.inl (.inr e))) ha hp.valueBranches ep eq
  obtain ⟨s, paths, scheduled, _, done⟩ := splice_schedule_proof (pe := pe) hp unpack rfl
  exact ⟨s, paths, scheduled, (Continuation.split_let₂ ha hb).trans (replay.trans done)⟩

private theorem replay_injection {Γ : VCtx (Ty α)} {A D : Ty α} {a injected value : Tm Φ}
    {p : Region Φ} {before : List (List Φ × Nat)}
    (ha : Tm.HasType Γ a A) (tag : Tm.BranchValue (A :: Γ) value D)
    (hp : Schedule Γ p [A] before) (ep : Continuation.Eqv pe Γ (returnOnce a) p [A])
    (split : Continuation.Eqv pe Γ (returnOnce injected) (.let₁ a (.br 0 value)) [D]) :
    ∃ s paths, Schedule Γ s [D] paths ∧ Continuation.Eqv pe Γ (returnOnce injected) s [D] := by
  have finish : Schedule (A :: Γ) (.br 0 value : Region Φ) [D] [([], 0)] := .ret (i := 0) rfl tag
  obtain ⟨s, paths, scheduled, _, done⟩ := splice_schedule_proof (pe := pe) hp finish rfl
  have composed := append_eq pe (UnaryReturn.returnOnce_valueBranches ha) hp.valueBranches ep
    (Extension.Eqv.refl finish.valueBranches.hasType)
  rw [append_return] at composed
  exact ⟨s, paths, scheduled, split.trans (composed.trans done)⟩

private theorem replay_abort {Γ : VCtx (Ty α)} {D : Ty α} {a : Tm Φ} {p : Region Φ}
    {before : List (List Φ × Nat)} (ha : Tm.HasType Γ a Ty.empty)
    (hp : Schedule Γ p [Ty.empty] before) (ep : Continuation.Eqv pe Γ (returnOnce a) p [Ty.empty]) :
    ∃ s, Schedule Γ s [D] [] ∧ Continuation.Eqv pe Γ (returnOnce (.abort a)) s [D] := by
  have finish : Schedule (Ty.empty :: Γ) (returnOnce (.abort (.var 0)) : Region Φ) [D] [] :=
    .abortValue (.var (i := 0) rfl) (.ret (i := 0) rfl (.var (i := 0) rfl))
  obtain ⟨s, paths, scheduled, sub, done⟩ := splice_schedule_proof (pe := pe) hp finish rfl
  have emptyPaths (prior : List (List Φ × Nat)) : appendPaths prior [] = [] := by
    induction prior with
    | nil => rfl
    | cons _ _ ih => simpa only [appendPaths, List.flatMap_cons, List.map_nil, List.nil_append] using ih
  have noExit := List.eq_nil_of_sublist_nil (emptyPaths before ▸ sub)
  have composed := append_eq pe (UnaryReturn.returnOnce_valueBranches ha) hp.valueBranches ep
    (Extension.Eqv.refl finish.valueBranches.hasType)
  rw [append_return] at composed
  exact ⟨s, noExit ▸ scheduled, (Continuation.split_abort ha).trans (composed.trans done)⟩

private theorem replay_pair {Γ : VCtx (Ty α)} {A B : Ty α} {a b : Tm Φ} {p q : Region Φ}
    {before after : List (List Φ × Nat)}
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B)
    (hp : Schedule Γ p [A] before) (hq : Schedule Γ q [B] after)
    (ep : Continuation.Eqv pe Γ (returnOnce a) p [A])
    (eq : Continuation.Eqv pe Γ (returnOnce b) q [B]) :
    ∃ s paths, Schedule Γ s [product A B] paths ∧ Continuation.Eqv pe Γ (returnOnce (.pair a b)) s [product A B] := by
  have hq' := Continuation.rename_schedule hq (Ren.wk Γ A)
  have hb' := hb.rename (Ren.wk Γ A)
  have eq' := eq.renameVars (Ren.wk Γ A)
  change Continuation.Eqv pe (A :: Γ) (returnOnce (b.rename Nat.succ)) (q.renameVars Nat.succ) [B] at eq'
  have finish : Schedule (B :: A :: Γ) (.br 0 (.pair (.var 1) (.var 0)) : Region Φ)
      [product A B] [([], 0)] := .ret (i := 0) rfl (.pair (.var rfl) (.var rfl))
  obtain ⟨tail, _, t, _, et⟩ := splice_schedule_proof (pe := pe) hq' finish rfl
  have moved := append_eq pe (UnaryReturn.returnOnce_valueBranches hb') hq'.valueBranches eq'
    (Extension.Eqv.refl finish.valueBranches.hasType)
  rw [append_return] at moved
  obtain ⟨s, paths, scheduled, _, done⟩ := splice_schedule_proof (pe := pe) hp t rfl
  have composed := append_eq pe (UnaryReturn.returnOnce_valueBranches ha) hp.valueBranches ep (moved.trans et)
  rw [append_return] at composed
  have split : OrderedPairs.Eqv pe Γ (returnOnce (.pair a b)) (pairSequence a b) [product A B] :=
    .extra (UnaryReturn.returnOnce_valueBranches (.pair ha hb)).hasType
      (WithPairReturns.pairSequence_typed ha hb).hasType (.inr (.seq ha hb))
  exact ⟨s, paths, scheduled, (ofOrdered pe split).trans (composed.trans done)⟩

private theorem replay_call {Γ : VCtx (Ty α)} {f : Φ} {a : Tm Φ} {p : Region Φ}
    {paths : List (List Φ × Nat)} (ha : Tm.HasType Γ a (instrSrc f))
    (h : Schedule Γ p [instrSrc f] paths) (e : Continuation.Eqv pe Γ (returnOnce a) p [instrSrc f]) :
    ∃ s routes, Schedule Γ s [instrTrg f] routes ∧ Continuation.Eqv pe Γ (returnOnce (.op f a)) s [instrTrg f] := by
  have invoked : Schedule (instrSrc f :: Γ) (Continuation.invoke f (.br 0 (.var 0))) [instrTrg f] [([f], 0)] :=
    .call (.var (i := 0) rfl) (.ret (i := 0) rfl (.var (i := 0) rfl))
  obtain ⟨s, routes, scheduled, _, done⟩ := splice_schedule_proof (pe := pe) h invoked rfl
  have step := ConstructorJoin.ofCall (pe := pe) (Step.seq f ha)
  have replay := append_eq pe (returnRegion_typed ha) h.valueBranches ((returns_one pe ha).trans e)
    (Extension.Eqv.refl (UnaryReturn.returnOnce_valueBranches
      (Tm.HasType.op (f := f) (.var (i := 0) rfl))).hasType)
  exact ⟨s, routes, scheduled, (ofCalls pe step).trans (replay.trans done)⟩

private theorem replay_case {Γ : VCtx (Ty α)} {A B D : Ty α} {e l r : Tm Φ} {p q s : Region Φ}
    {before left right : List (List Φ × Nat)}
    (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l D) (hr : Tm.HasType (B :: Γ) r D)
    (hp : Schedule Γ p [coprod A B] before) (hq : Schedule (A :: Γ) q [D] left) (hs : Schedule (B :: Γ) s [D] right)
    (ep : Continuation.Eqv pe Γ (returnOnce e) p [coprod A B])
    (eq : Continuation.Eqv pe (A :: Γ) (returnOnce l) q [D])
    (es : Continuation.Eqv pe (B :: Γ) (returnOnce r) s [D]) :
    ∃ out paths, Schedule Γ out [D] paths ∧ Continuation.Eqv pe Γ (returnOnce (.case e l r)) out [D] := by
  have dispatch : Schedule (coprod A B :: Γ) (boundCase q s) [D] (left ++ right) :=
    .caseVar (slot := 0) rfl (Continuation.rename_schedule hq ((Ren.wk Γ (coprod A B)).lift A))
      (Continuation.rename_schedule hs ((Ren.wk Γ (coprod A B)).lift B))
  have bind := WithCaseBind.case_eq_let (Seed := Continuation.Seed pe) (fun e => .inl (.inr e)) he
    hq.valueBranches hs.valueBranches
  have replay := append_eq pe (UnaryReturn.returnOnce_valueBranches he) hp.valueBranches ep
    (Extension.Eqv.refl dispatch.valueBranches.hasType)
  rw [append_return] at replay
  obtain ⟨out, paths, scheduled, _, done⟩ := splice_schedule_proof (pe := pe) hp dispatch rfl
  exact ⟨out, paths, scheduled, (Continuation.split_return he hl hr).trans
    ((Extension.Eqv.case he eq es).trans (bind.trans (replay.trans done)))⟩

theorem normalize_proof {n : Nat} {β : BoundCtx (Ty α) n} {t : LetCase.LocallyNameless.Tm Empty Φ n}
    {D : Ty α} (d : Derivation Φ (.nil : Ctx Empty (Ty α)) β t D) (shape : Admitted (erase t)) :
    ∃ s paths, Schedule β.toList s [D] paths ∧ Continuation.Eqv pe β.toList (returnOnce (erase t)) s [D] := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | @bv _ β i =>
    exact pure_leaf pe (.var (BoundCtx.getElem?_toList β i))
  | unit => exact pure_leaf pe .unit
  | inl d ih =>
    obtain ⟨_, _, h, replay⟩ := ih shape
    have typed := erase_hasType d.toHasType
    exact replay_injection pe typed (.inl (.var (i := 0) rfl)) h replay (Continuation.split_inl typed)
  | inr d ih =>
    obtain ⟨_, _, h, replay⟩ := ih shape
    have typed := erase_hasType d.toHasType
    exact replay_injection pe typed (.inr (.var (i := 0) rfl)) h replay (Continuation.split_inr typed)
  | op d ih =>
    obtain ⟨_, _, h, replay⟩ := ih shape
    exact replay_call pe (erase_hasType d.toHasType) h replay
  | let₁ a b iha ihb =>
    obtain ⟨_, _, ha, ea⟩ := iha shape.1
    obtain ⟨_, _, hb, eb⟩ := ihb shape.2
    exact replay_let pe (erase_hasType a.toHasType) (erase_hasType b.toHasType) ha hb ea eb
  | pair a b iha ihb =>
    obtain ⟨_, _, ha, ea⟩ := iha shape.1
    obtain ⟨_, _, hb, eb⟩ := ihb shape.2
    exact replay_pair pe (erase_hasType a.toHasType) (erase_hasType b.toHasType) ha hb ea eb
  | case e l r ihe ihl ihr =>
    obtain ⟨_, _, he, ee⟩ := ihe shape.1
    obtain ⟨_, _, hl, el⟩ := ihl shape.2.1
    obtain ⟨_, _, hr, er⟩ := ihr shape.2.2
    exact replay_case pe (erase_hasType e.toHasType) (erase_hasType l.toHasType) (erase_hasType r.toHasType)
      he hl hr ee el er
  | let₂ a b iha ihb =>
    obtain ⟨_, _, ha, ea⟩ := iha shape.1
    obtain ⟨_, _, hb, eb⟩ := ihb shape.2
    exact replay_let₂ pe (erase_hasType a.toHasType) (erase_hasType b.toHasType) ha hb ea eb
  | abort d ih =>
    obtain ⟨_, _, h, replay⟩ := ih shape
    obtain ⟨s, scheduled, done⟩ := replay_abort pe (erase_hasType d.toHasType) h replay
    exact ⟨s, [], scheduled, done⟩

private theorem singleton_labels {D : Ty α} {L : LCtx (Ty α)} {i : Nat} (out : At L i D) :
    Ren [D] L (fun _ => i) :=
  fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ out

private theorem guarded_rename {n : Nat} {β : BoundCtx (Ty α) n} {D : Ty α} (c : Code Φ β D)
    (i : Nat) (ρ : Nat → Nat) :
    (c.guardedSSA i).renameLabels ρ = c.guardedSSA (ρ i) := by
  rw [Code.guardedSSA, ← Region.bindBranchArguments_renameLabels, Code.toSSA_renameLabels]
  rfl

private theorem reflexive_return {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {D : Ty α}
    (d : Derivation Φ (.nil : Ctx Empty (Ty α)) β t D) {L : LCtx (Ty α)} {i : Nat} (out : At L i D) :
    Continuation.Eqv pe β.toList ((Code.br ⟨t, d⟩).guardedSSA i) ((Code.br ⟨t, d⟩).guardedSSA i) L :=
  .refl ((Code.br ⟨t, d⟩).guardedSSA_valueBranches out).hasType

private theorem reify {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {D : Ty α}
    (d : Derivation Φ (.nil : Ctx Empty (Ty α)) β t D) (shape : Admitted (erase t))
    {L : LCtx (Ty α)} {i : Nat} (out : At L i D) :
    Continuation.Eqv pe β.toList ((Code.br ⟨t, d⟩).guardedSSA i) ((Code.ofLetCase d).guardedSSA i) L := by
  induction d generalizing L i with
  | @fv _ _ x _ _ => exact x.elim
  | @let₁ _ β _ _ A D da db iha ihb =>
    have ha := erase_hasType da.toHasType
    have hb := erase_hasType db.toHasType
    have entry := iha shape.1 (rfl : At (A :: L) 0 A)
    have body := ihb shape.2 out
    have bodyTyped := (Code.ofLetCase db).guardedSSA_valueBranches out
    have forward := (unary pe (.fuse ha hb)).symm.renameLabels (singleton_labels out)
    have linked := Region.Paper.linkedJoin (UnaryReturn.returnOnce_valueBranches ha) bodyTyped
    rw [append_return, guarded_rename] at linked
    let R : Fin 1 → Ty α := fun _ => A
    have rows : List.ofFn R ++ L = A :: L := by simp [R, List.ofFn_succ]
    have shifted := (Code.ofLetCase db).guardedSSA_valueBranches ((Ren.wk L A) out)
    have cfg := Extension.Eqv.cfg (Seed := Continuation.Seed pe) R (rows.symm ▸ entry)
      (fun _ => rows.symm ▸ Extension.Eqv.refl shifted.hasType)
    exact forward.trans ((Extension.Eqv.let₁ ha body).trans ((Extension.Eqv.paper linked.symm).trans cfg))
  | case de dl dr _ ihl ihr =>
    have he := erase_hasType de.toHasType
    have split := Continuation.split_return (pe := pe) he (erase_hasType dl.toHasType) (erase_hasType dr.toHasType)
    exact (split.renameLabels (singleton_labels out)).trans
      (Extension.Eqv.case he (ihl shape.2.1 out) (ihr shape.2.2 out))
  | let₂ da db _ ihb =>
    have ha := erase_hasType da.toHasType
    have split := Continuation.split_let₂ (pe := pe) ha (erase_hasType db.toHasType)
    exact (split.renameLabels (singleton_labels out)).trans (Extension.Eqv.let₂ ha (ihb shape.2 out))
  | abort a _ => exact reflexive_return pe (.abort a) out
  | bv => exact reflexive_return pe .bv out
  | unit => exact reflexive_return pe .unit out
  | op a _ => exact reflexive_return pe (.op a) out
  | pair a b _ _ => exact reflexive_return pe (.pair a b) out
  | inl a _ => exact reflexive_return pe (.inl a) out
  | inr a _ => exact reflexive_return pe (.inr a) out

theorem normalize_at_proof {n : Nat} {β : BoundCtx (Ty α) n} {D : Ty α} {L : LCtx (Ty α)}
    {i : Nat} (out : At L i D) (a : Operand Φ β D) (shape : Admitted (erase a.1)) :
    ∃ s, ∃ paths : List (List Φ), Schedule β.toList s L (paths.map fun fs => (fs, i)) ∧
      Continuation.Eqv pe β.toList ((Code.br a).guardedSSA i) s L ∧
      Continuation.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA i) s L := by
  obtain ⟨s, paths, h, replay⟩ := normalize_proof pe a.2 shape
  have written := replay.renameLabels (singleton_labels out)
  exact ⟨_, paths.map Prod.fst, by
    simpa only [List.map_map, Function.comp_def] using retarget_schedule_proof out h rfl,
    written, (reify pe a.2 shape out).symm.trans written⟩

theorem normalize_abort_at_proof {n : Nat} {β : BoundCtx (Ty α) n} {D : Ty α} {L : LCtx (Ty α)}
    {i : Nat} (out : At L i D) (a : Operand Φ β Ty.empty) (shape : Admitted (erase a.1)) :
    ∃ s, Schedule β.toList s L [] ∧
      Continuation.Eqv pe β.toList ((Code.br ⟨.abort a.1, .abort (C := D) a.2⟩).guardedSSA i) s L ∧
      Continuation.Eqv pe β.toList ((Code.ofLetCase (.abort (C := D) a.2)).guardedSSA i) s L := by
  obtain ⟨_, _, h, replay⟩ := normalize_proof pe a.2 shape
  obtain ⟨s, scheduled, done⟩ := replay_abort pe (erase_hasType a.2.toHasType) h replay
  have written := done.renameLabels (singleton_labels out)
  exact ⟨_, retarget_schedule_proof out scheduled rfl, written, written⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive
