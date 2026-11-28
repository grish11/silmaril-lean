module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms

/-! # Native reductions for ranked packet-local tables -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RankedReplyRecognition

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies (Atom Profile ReplyShape)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic (Control)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked

variable {Φ : Type} [Profile Φ]

private theorem packet_subst {s : ReplyShape} {L : LCtx (Ty Atom)} {r : Region Φ}
    (hr : HasType [s.ty] r L) {θ : Nat → Tm Φ} (hθ : θ 0 = .var 0) :
    r.substVars θ = r :=
  (Paper.SingletonReification.SingleCfg.singleton_subst hr hθ).trans (substVars_var r)

private theorem packet_rename {s : ReplyShape} {L : LCtx (Ty Atom)} {r : Region Φ}
    (hr : HasType [s.ty] r L) {ρ : Nat → Nat} (hρ : ρ 0 = 0) :
    r.renameVars ρ = r := by
  rw [renameVars_eq_substVars]
  exact packet_subst hr (congrArg Tm.var hρ)

private theorem packet_ren (s : ReplyShape) (Γ : VCtx (Ty Atom)) :
    SSA.Ren [s.ty] (s.ty :: Γ) id := by
  intro i A hi
  cases i with
  | zero => simpa [At] using hi
  | succ i => simp [At] at hi

private theorem packet_scope {s : ReplyShape} {Γ L : List (Ty Atom)} {r : Region Φ}
    (hr : HasType [s.ty] r L) : HasType (s.ty :: Γ) r L := by
  simpa only [renameVars_id] using hr.renameVars (packet_ren s Γ)

private theorem packet_values {s : ReplyShape} {Γ L : List (Ty Atom)} {r : Region Φ}
    (hr : ValueBranches [s.ty] r L) : ValueBranches (s.ty :: Γ) r L := by
  simpa only [renameVars_id] using hr.renameVars (packet_ren s Γ)

variable {n : Nat} {R : Fin n → ReplyShape} {t : ReplyShape}

private abbrev context (R : Fin n → ReplyShape) (t : ReplyShape) :=
  List.ofFn (fun i => (R i).ty) ++ [t.ty]

private theorem local_at (i : Fin n) : At (context R t) i (R i).ty := by
  change (List.ofFn (fun i => (R i).ty) ++ [t.ty])[(i : Nat)]? = _
  rw [List.getElem?_append_left (by simp)]
  simp

private theorem block_typed {s : ReplyShape} (b : Block (Φ := Φ) R t s) :
    ValueBranches [s.ty] b.region (context R t) := by
  induction b with
  | jump j hs => exact .br (local_at (t := t) j) (.var (by simp [At, hs]))
  | exit p =>
      simp only [Block.region, renameLabels_eq_lsubst]
      apply p.region_typed.lsubst
      intro i A hi
      refine .br ?_ (.var rfl)
      have h₀ := List.mem_singleton.mp (List.mem_of_getElem? hi)
      have hᵢ : i = 0 := by
        cases i with
        | zero => rfl
        | succ i => simp [At] at hi
      subst i A
      simp [context, At]

  | case _ _ hl hr => exact .case (.var rfl) (packet_values hl) (packet_values hr)
  | request _ _ _ ih => exact .let₁ (.op (.var rfl)) (packet_values ih)

private abbrev table (blocks : (i : Fin n) → Block (Φ := Φ) R t (R i)) :=
  fun i => (blocks i).region

private theorem enter_block (raw : Fin n → Region Φ)
    (rows : ∀ i, ValueBranches [(R i).ty] (raw i) (context R t))
    (i : Fin n) {Γ : VCtx (Ty Atom)} :
    Paper.Eqv ((R i).ty :: Γ) (.cfg (.br i (.var 0)) n raw)
      (.cfg (raw i) n raw) [t.ty] := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      refine (Paper.Eqv.cfgEta (.native (.base (.entry
        (.cfgBrLocal (fun j => (R j).ty) i (.var rfl) (fun j => (packet_values (rows j)).hasType)))))).trans ?_
      refine Paper.Eqv.cfg (fun j => (R j).ty) ?_
        (fun j => Paper.Eqv.refl (packet_values (rows j)).hasType)
      have h := packet_subst (rows i).hasType
        (show Tm.singleSubst (.var 0 : Tm Φ) 0 = .var 0 from rfl)
      have beta := SubstitutionEquiv.letValue (.var (i := 0) rfl)
        (packet_values (Γ := (R i).ty :: Γ) (rows i)).hasType
      rw [h] at beta
      exact .cfgEta (.native beta)

private theorem leave_block (raw : Fin n → Region Φ)
    (rows : ∀ i, ValueBranches [(R i).ty] (raw i) (context R t))
    {s : ReplyShape} {Γ : VCtx (Ty Atom)} (p : Control Φ s t) :
    Paper.Eqv (s.ty :: Γ) (.cfg ((Block.exit p : Block R t s).region) n raw)
      p.region [t.ty] := by
  cases n with
  | zero =>
      simp only [Block.region, Nat.zero_add]
      rw [show (fun j : Nat => j) = id from rfl, renameLabels_id]
      exact .cfgEta (.native (.base (.entry (.cfgZero (packet_scope p.region_typed.hasType) _))))
  | succ n => exact .cfgEta (.native (.cfgOutward (fun j => (R j).ty)
                (packet_scope p.region_typed.hasType) (fun j => (packet_values (rows j)).hasType)))

private theorem reindex_sound {s u : ReplyShape} {Γ : VCtx (Ty Atom)} {raw : Region Φ}
    (hs : s = u) {p : Control Φ s t} (eq : Paper.Eqv (s.ty :: Γ) raw p.region [t.ty]) :
    Paper.Eqv (u.ty :: Γ) raw (show Control Φ u t from hs ▸ p).region [t.ty] := by
  cases hs
  exact eq

private theorem subst_case_entry (raw : Fin n → Region Φ)
    (rows : ∀ i, ValueBranches [(R i).ty] (raw i) (context R t))
    {l r : ReplyShape} {left right : Region Φ}
    (hl : HasType [l.ty] left (context R t)) (hr : HasType [r.ty] right (context R t))
    (θ : Nat → Tm Φ) :
    (.cfg (.case (.var 0) left right) n raw : Region Φ).substVars θ =
      .cfg (.case (θ 0) left right) n raw := by
  simp only [Region.substVars, Tm.subst, packet_subst hl (θ := Tm.liftSubst θ) rfl,
    packet_subst hr (θ := Tm.liftSubst θ) rfl]
  congr 1
  funext j
  exact packet_subst (rows j).hasType (θ := Tm.liftSubst θ) rfl

private theorem case_cfg (raw : Fin n → Region Φ)
    (rows : ∀ i, ValueBranches [(R i).ty] (raw i) (context R t))
    {Γ : VCtx (Ty Atom)} {l r : ReplyShape} {left right : Region Φ}
    (hl : HasType [l.ty] left (context R t)) (hr : HasType [r.ty] right (context R t)) :
    Paper.Eqv ((ReplyShape.sum l r).ty :: Γ) (.cfg (.case (.var 0) left right) n raw)
      (.case (.var 0) (.cfg left n raw) (.cfg right n raw)) [t.ty] := by
  let S := (ReplyShape.sum l r).ty
  have hbody : HasType (S :: S :: Γ) (.cfg (.case (.var 0) left right) n raw) [t.ty] :=
    .cfg (fun j => (R j).ty)
      (.case (.var rfl) (packet_scope hl) (packet_scope hr)) (fun j => (packet_values (rows j)).hasType)
  have split := Paper.Eqv.cfgEta (.native
    (SubstitutionEquiv.caseValue (.var (Γ := S :: Γ) (i := 0) rfl) hbody))
  simp only [subst_case_entry raw rows hl hr, Tm.replaceNewest, Tm.singleSubst, Tm.consSubst] at split
  apply split.symm.trans
  refine Paper.Eqv.case (A := l.ty) (B := r.ty) (.var rfl) ?_ ?_
  · refine Paper.Eqv.cfg (fun j => (R j).ty) ?_
      (fun j => Paper.Eqv.refl (packet_values (rows j)).hasType)
    refine (Paper.Eqv.cfgEta (.native (.base
      (.caseInl (.var rfl) (packet_scope hl) (packet_scope hr))))).trans ?_
    have beta := SubstitutionEquiv.letValue (.var (Γ := l.ty :: S :: Γ) (i := 0) rfl) (packet_scope hl)
    rw [packet_subst hl (θ := Tm.singleSubst (.var 0)) rfl] at beta
    exact .cfgEta (.native beta)
  · refine Paper.Eqv.cfg (fun j => (R j).ty) ?_
      (fun j => Paper.Eqv.refl (packet_values (rows j)).hasType)
    refine (Paper.Eqv.cfgEta (.native (.base
      (.caseInr (.var rfl) (packet_scope hl) (packet_scope hr))))).trans ?_
    have beta := SubstitutionEquiv.letValue (.var (Γ := r.ty :: S :: Γ) (i := 0) rfl) (packet_scope hr)
    rw [packet_subst hr (θ := Tm.singleSubst (.var 0)) rfl] at beta
    exact .cfgEta (.native beta)

private theorem inline_sound (raw : Fin n → Region Φ)
    (rows : ∀ i, ValueBranches [(R i).ty] (raw i) (context R t))
    (next : (i : Fin n) → Option (Control Φ (R i) t))
    (jump_sound : ∀ (j : Fin n) (Γ : VCtx (Ty Atom)) {p : Control Φ (R j) t}, next j = some p →
      Paper.Eqv ((R j).ty :: Γ) (.cfg (.br j (.var 0)) n raw) p.region [t.ty])
    {s : ReplyShape} (b : Block (Φ := Φ) R t s) {Γ : VCtx (Ty Atom)} {p : Control Φ s t}
    (h : b.inline next = some p) :
    Paper.Eqv (s.ty :: Γ) (.cfg b.region n raw) p.region [t.ty] := by
  induction b generalizing Γ with
  | jump j hs =>
      obtain ⟨q, hq, hqp⟩ := Option.map_eq_some_iff.mp h
      subst p
      exact reindex_sound hs (jump_sound j Γ hq)
  | exit q =>
      have hp : q = p := Option.some.inj h
      subst p
      exact leave_block raw rows q
  | case l r ihl ihr =>
      obtain ⟨pl, hl, tail⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨pr, hr, hp⟩ := Option.bind_eq_some_iff.mp tail
      cases hp
      refine (case_cfg raw rows (block_typed l).hasType (block_typed r).hasType).trans ?_
      simp only [Control.region, packet_rename pl.region_typed.hasType (ρ := lift Nat.succ) rfl,
        packet_rename pr.region_typed.hasType (ρ := lift Nat.succ) rfl]
      exact .case (.var rfl) (ihl hl) (ihr hr)
  | request op move body ih =>
      obtain ⟨q, hq, hp⟩ := Option.map_eq_some_iff.mp h
      subst p
      have ha : Tm.HasType (ReplyShape.unit.ty :: Γ) (.op op (.var 0)) (Profile.reply op).ty :=
        .op (.var rfl)
      have step := move (fun j => (R j).ty)
        ha (packet_values (block_typed body)) (fun j => packet_values (rows j))
      have keep (j : Fin n) :
          (raw j).renameVars (lift Nat.succ) = raw j :=
        packet_rename (rows j).hasType rfl
      simp only [keep] at step
      rw [call_region op q, packet_rename q.region_typed.hasType (ρ := lift Nat.succ) rfl]
      exact step.trans (.let₁ ha (ih hq))

private theorem follow_sound (blocks : (i : Fin n) → Block (Φ := Φ) R t (R i))
    {Γ : VCtx (Ty Atom)} {fuel : Nat} {i : Fin n} {p : Control Φ (R i) t}
    (h : follow blocks fuel i = some p) :
    Paper.Eqv ((R i).ty :: Γ) (.cfg (.br i (.var 0)) n (table blocks)) p.region [t.ty] := by
  induction fuel generalizing Γ i with
  | zero => cases h
  | succ fuel ih =>
      exact (enter_block (table blocks) (fun j => block_typed (blocks j)) i).trans
        (inline_sound (table blocks) (fun j => block_typed (blocks j)) (follow blocks fuel) (fun _ _ _ eq => ih eq) (blocks i) h)

variable [DecidableEq Φ]

private theorem checkBlock_sound (allowed : Fin n → Bool) {policy : RequestPolicy Φ n} {s : ReplyShape} {raw : Region Φ}
    {b : Block (Φ := Φ) R t s} (h : checkBlock R allowed s t raw policy = some b) : raw = b.region := by
  unfold checkBlock at h
  obtain ⟨c, _, hc⟩ := Option.bind_eq_some_iff.mp h
  split at hc
  · rename_i matched
    cases hc
    exact sameBody_eq matched
  · cases hc

private theorem entry_sound (rank : Fin n → Nat) (blocks : (i : Fin n) → Block (Φ := Φ) R t (R i))
    {s : ReplyShape} {entry : Region Φ} {p : Control Φ s t} {policy : RequestPolicy Φ n}
    (h : runEntry rank blocks s entry policy = some p) :
    Paper.Eqv [s.ty] (.cfg entry n (table blocks)) p.region [t.ty] := by
  obtain ⟨b, hb, he⟩ := Option.bind_eq_some_iff.mp h
  rw [checkBlock_sound (fun _ => true) hb]
  exact inline_sound (table blocks) (fun j => block_typed (blocks j))
    (fun i => follow blocks (rank i + 1) i)
    (fun _ _ _ eq => follow_sound blocks eq) b he

private theorem collect_sound (rank : Fin n → Nat) {policy : RequestPolicy Φ n} {raw : Fin n → Region Φ}
    {blocks : (i : Fin n) → Block (Φ := Φ) R t (R i)}
    (h : collect R rank t raw policy = some blocks) :
    raw = table blocks := by
  simp only [collect] at h
  split at h
  · rename_i all
    cases h
    funext i
    exact checkBlock_sound (fun j => decide (rank j < rank i)) (Option.some_get (all i)).symm
  · cases h

theorem sound (R : Fin n → ReplyShape) (rank : Fin n → Nat)
    {s t : ReplyShape} {raw : Region Φ} {p : Control Φ s t} {policy : RequestPolicy Φ n}
    (h : recognize R rank s t raw policy = some p) :
    Paper.Eqv [s.ty] raw p.region [t.ty] := by
  cases raw <;> try (change none = some p at h; cases h)
  case cfg entry k raw =>
    change (if h : k = n then (collect R rank t (h ▸ raw) policy).bind (fun blocks =>
      runEntry rank blocks s entry policy) else none) = some p at h
    split at h
    · rename_i hk
      subst k
      change ((collect R rank t raw policy).bind fun blocks => runEntry rank blocks s entry policy) = some p at h
      obtain ⟨blocks, hb, he⟩ := Option.bind_eq_some_iff.mp h
      rw [collect_sound rank hb]
      exact entry_sound rank blocks he
    · cases h


private theorem graph_typed {last : Region Ranked.Example.Op}
    (hlast : ValueBranches [ReplyShape.unit.ty, Ranked.Example.Reply.ty] last
      [Ranked.Example.Reply.ty, ReplyShape.unit.ty, ReplyShape.unit.ty, ReplyShape.unit.ty,
        Ranked.Example.Reply.ty]) :
    ValueBranches [Ranked.Example.Reply.ty] (Ranked.Example.graph last) [Ranked.Example.Reply.ty] := by
  refine .cfg (fun i => (Ranked.Example.packets i).ty)
    (.br rfl (.var rfl)) ?_
  refine Fin.cases (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))) (fun j => ?_)
  refine Fin.cases (.br rfl (.var rfl)) (fun k => ?_) j
  refine Fin.cases (.br rfl (.var rfl)) (fun m => ?_) k
  rw [Fin.eq_zero m]
  exact hlast

theorem accepted_typed : ValueBranches [Ranked.Example.Reply.ty] Ranked.Example.accepted [Ranked.Example.Reply.ty] :=
  graph_typed (.let₁ (.op (.var rfl)) (.br rfl (.var rfl)))

theorem backEdge_typed : ValueBranches [Ranked.Example.Reply.ty] Ranked.Example.backEdge [Ranked.Example.Reply.ty] :=
  graph_typed (.br rfl (.var rfl))

theorem captured_typed : ValueBranches [Ranked.Example.Reply.ty] Ranked.Example.captured [Ranked.Example.Reply.ty] :=
  graph_typed (.br rfl (.var rfl))

private theorem request_graph_typed {next : Region RequestExample.Op}
    (hn : ValueBranches [ReplyShape.unit.ty, ReplyShape.unit.ty] next
      [ReplyShape.unit.ty, ReplyShape.unit.ty]) :
    ValueBranches [ReplyShape.unit.ty] (RequestExample.graph next) [ReplyShape.unit.ty] :=
  .cfg (fun _ : Fin 1 => ReplyShape.unit.ty)
    (.let₁ (.op (.var rfl)) (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))))
    (fun _ => hn)

theorem request_accepted_typed : ValueBranches [ReplyShape.unit.ty] RequestExample.accepted
    [ReplyShape.unit.ty] :=
  request_graph_typed (.let₁ (.op (.var rfl)) (.br rfl (.var rfl)))

theorem request_backEdge_typed : ValueBranches [ReplyShape.unit.ty] RequestExample.backEdge
    [ReplyShape.unit.ty] :=
  request_graph_typed (.br rfl (.var rfl))

theorem request_captured_typed : ValueBranches [ReplyShape.unit.ty] RequestExample.captured
    [ReplyShape.unit.ty] :=
  request_graph_typed (.br rfl (.var rfl))

private theorem request_flat_rows (j : Fin 2) :
    ValueBranches [(RequestExample.flatPackets j).ty] (RequestExample.flatBlocks j)
      (context RequestExample.flatPackets .unit) :=
  Fin.cases
    (.let₁ (.op (.var rfl)) (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))))
    (fun _ => .let₁ (.op (.var rfl)) (.br rfl (.var rfl))) j

theorem request_flat_typed : ValueBranches [ReplyShape.unit.ty] RequestExample.flat
    [ReplyShape.unit.ty] :=
  .cfg (fun i => (RequestExample.flatPackets i).ty) (.br rfl (.var rfl))
    (fun i => packet_values (request_flat_rows i))

theorem request_flat_entry :
    Paper.Eqv [ReplyShape.unit.ty] RequestExample.flat RequestExample.flatEntered
      [ReplyShape.unit.ty] :=
  enter_block RequestExample.flatBlocks request_flat_rows 0

private def tick : Control RequestExample.Op .unit .unit :=
  .let₁ (.call .tick) (.forward .unit)

private theorem request_flat_tail {Γ : VCtx (Ty Atom)} :
    Paper.Eqv ((Profile.reply (Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Example.Op.read)).ty :: Γ)
      (.cfg (RequestExample.choose 1) 2 RequestExample.flatBlocks)
      (Control.case tick tick).region [ReplyShape.unit.ty] := by
  let next : (i : Fin 2) → Option (Control RequestExample.Op (RequestExample.flatPackets i) .unit) :=
    Fin.cases none (fun _ => some tick)
  have jumps : ∀ (i : Fin 2) (Δ : VCtx (Ty Atom)) {p}, next i = some p →
      Paper.Eqv ((RequestExample.flatPackets i).ty :: Δ)
        (.cfg (.br i (.var 0)) 2 RequestExample.flatBlocks) p.region [ReplyShape.unit.ty] := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro Δ p h
      change none = some p at h
      cases h
    · rw [Fin.eq_zero j]
      intro Δ p h
      change some tick = some p at h
      cases h
      exact (enter_block RequestExample.flatBlocks request_flat_rows 1).trans
        (leave_block RequestExample.flatBlocks request_flat_rows tick)
  exact inline_sound RequestExample.flatBlocks request_flat_rows next jumps
    (.case (.jump 1 rfl) (.jump 1 rfl)) rfl

theorem request_flat_moved :
    Paper.Eqv [ReplyShape.unit.ty] RequestExample.flatMoved RequestExample.expected.region
      [ReplyShape.unit.ty] := by
  change Paper.Eqv _ _ (Control.let₁ (.call (Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Example.Op.read)) (.case tick tick)).region _
  rw [call_region, packet_rename (Control.case tick tick).region_typed.hasType
    (ρ := lift Nat.succ) rfl]
  exact .let₁ (.op (.var rfl)) request_flat_tail

theorem request_flat_move_iff :
    Paper.Eqv [ReplyShape.unit.ty] RequestExample.flatEntered RequestExample.flatMoved
      [ReplyShape.unit.ty] ↔
    Paper.Eqv [ReplyShape.unit.ty] RequestExample.flat RequestExample.expected.region
      [ReplyShape.unit.ty] :=
  ⟨fun h => request_flat_entry.trans (h.trans request_flat_moved),
    fun h => request_flat_entry.symm.trans (h.trans request_flat_moved.symm)⟩

open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies (Row)

theorem request_readback :
    RequestExample.expected.readback PUnit.unit = RequestExample.expectedRow := by
  change Row.call (Φ := RequestExample.Op) .read _ = _
  congr 1
  funext x
  cases x <;> rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RankedReplyRecognition
