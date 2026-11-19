module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Det
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.Exp
public import Silmaril.Wasm.Component.Reference.LinkedGComp.Defs
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete

/-!
# Determinism of the two sides of a link (proofs)

* `not_inf_of_nf`: at `profile o`, a thread that reaches a normal form host-free does not also
  run host-free forever. `Internal o` is only deterministic up to bubbling (`Det.Join`), so this
  is not a consequence of the uniqueness of normal forms; the argument is `Binaryen.DetLift`'s
  `nf_not_div`, on threads: a lexicographic induction on the distance to the normal form
  (`NSteps.of_step_join`) and the size of the code (`Internal.shrink`: two different successors
  shrink the code).
* `not_trans_of_divB`: hence a running instance that diverges host-free (`Linked2.DivB`) makes
  no Proponent move.
* `agree_end`: two finished rounds of the importer (returning or diverging host-free) from the
  same state agree while their wired answers agree; `det_impTripleS`: the importer's triple is
  `AFun.Det` at `profile o`.
* `afunDet_sessTripleS_iff`: the exporter's triple is `AFun.Det` iff `ExpSpec.TDet ∧
  ExpSpec.DivExcl`; `retDet_sessTripleS`: `ExpSpec.Det` gives `RetDet`; `cexExp` meets
  `ExpSpec.Det` but its triple is not `AFun.Det`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile Internal NSteps tsize)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink (pmove_eq agree_cons impRel_agree
  op_ext typedQ_of_lowered lowered_forall₂ sumAns_inj)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-- `Reference.ImpRel` (a `SplitLink` structure of the same name is in scope). -/
local notation "RImpRel" => Silmaril.Wasm.Component.Reference.ImpRel

variable {o : GrowOracle}

/-! ## Host-free divergence excludes a normal form -/

/-- **A thread that reaches a normal form host-free does not run host-free forever**
(`profile o`). -/
theorem not_inf_of_nf {x y : Store Nat × STh}
    (hxy : Relation.ReflTransGen (Internal o) x y) (hy : ∀ z, ¬ Internal o y z) :
    ¬ ∃ g : ℕ → Store Nat × STh, g 0 = x ∧ ∀ k, Internal o (g k) (g (k + 1)) := by
  have hj : ∀ {a b c : Store Nat × STh}, Internal o a b → Internal o a c →
      Silmaril.Wasm.SingleThreaded.Det.Join (Internal o) b c :=
    fun h₁ h₂ => Silmaril.Wasm.SingleThreaded.Internal.deterministic h₁ h₂
  have aux : ∀ (k m : ℕ) (x : Store Nat × STh), tsize x = m → NSteps (Internal o) k x y →
      ∀ g : ℕ → Store Nat × STh, g 0 = x → (∀ n, Internal o (g n) (g (n + 1))) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro x hm hk g hg0 hg
    have hn : Internal o x (g 1) := hg0 ▸ hg 0
    have hg' : ∀ n, Internal o ((fun n => g (n + 1)) n) ((fun n => g (n + 1)) (n + 1)) :=
      fun n => hg (n + 1)
    cases hk with
    | refl => exact hy _ hn
    | @head _ a _ j h₁ hrest =>
      rcases Silmaril.Wasm.SingleThreaded.Internal.shrink hn h₁ with heq | hlt
      · exact ihk j (by omega) _ _ rfl (heq ▸ hrest) _ rfl hg'
      · obtain ⟨m', hm', hpath⟩ :=
          Silmaril.Wasm.SingleThreaded.NSteps.of_step_join hj hy (.head h₁ hrest) hn
        rcases Nat.lt_or_eq_of_le hm' with hlt' | rfl
        · exact ihk m' hlt' _ _ rfl hpath _ rfl hg'
        · exact ihm _ (by omega) _ rfl hpath _ rfl hg'
  rintro ⟨g, hg0, hg⟩
  obtain ⟨k, hk⟩ := Silmaril.Wasm.SingleThreaded.NSteps.of_rtg hxy
  exact aux k _ x rfl hk g hg0 hg

/-- **Host-free divergence excludes a host-free run to a normal form** (`profile o`). -/
theorem not_divB_of_reach {s : Store Nat} {t : STh} {y : Store Nat × STh}
    (hd : Linked2.DivB (profile o) s t) (h : Silmaril.Wasm.Game.Reach (profile o) (s, t) y)
    (hy : ∀ z, ¬ Silmaril.Wasm.Game.InternalP (profile o) y z) : False := by
  obtain ⟨g, hg0, hg⟩ := hd
  have e := Silmaril.Wasm.Game.internalP_profile (H := Nat) o
  unfold Silmaril.Wasm.Game.Reach at h
  rw [e] at h hy hg
  exact not_inf_of_nf h hy ⟨g, hg0, hg⟩

/-- **A running instance diverging host-free makes no move** (`profile o`). -/
theorem not_trans_of_divB {I : ScalarInstance} {f : I.F.Op} {s : Store Nat} {t : STh}
    {m : Move I.E I.F} {q : I.HState} (hd : Linked2.DivB (profile o) s t)
    (h : I.Trans (profile o) (.running f s t) m q) : False := by
  cases h with
  | ucall run callout _ =>
    exact not_divB_of_reach hd run (Silmaril.Wasm.Game.calloutAt_no_internal callout)
  | oret run final _ =>
    exact not_divB_of_reach hd run (Silmaril.Wasm.Game.resultAt_no_internal final)

/-! ## Finished rounds of the importer -/

variable {I : ScalarInstance} {b : SimpleI} {wire : List Nat}

/-- **A finished round of the importer from the hidden state `x`** after the core import calls
`cs`: it answers `w` and ends idle, or it runs host-free forever. -/
def RoundEnd (o : GrowOracle) (I : ScalarInstance) (b : SimpleI) (j : Fin b.exports.length)
    (f : I.F.Op) (x : I.HState) (cs : List (Σ e : I.E.Op, I.E.Ar e))
    (e : End (Store Nat) (Payload ⊕ PUnit.{1})) : Prop :=
  (∃ (w : I.F.Ar f) (u₁ : Store Nat),
      I.Path (profile o) x (callMoves cs ++ [.inr (.ans f w)]) (.idle u₁) ∧
      e = .ret (ExpSpec.sumAns (b.liftAns j w)) u₁) ∨
    (∃ (s : Store Nat) (t : STh), I.Path (profile o) x (callMoves cs) (.running f s t) ∧
      Linked2.DivB (profile o) s t ∧ e = .div)

variable {j : Fin b.exports.length} {f : I.F.Op}

theorem roundEnd_cons {x : I.HState} {m : I.E.Op} {n : I.E.Ar m}
    {cs : List (Σ e : I.E.Op, I.E.Ar e)} {e : End (Store Nat) (Payload ⊕ PUnit.{1})}
    (h : RoundEnd o I b j f x (⟨m, n⟩ :: cs) e) :
    ∃ q₁ q₂, I.Trans (profile o) x (.inl (.ask m)) q₁ ∧
      I.Trans (profile o) q₁ (.inl (.ans m n)) q₂ ∧ RoundEnd o I b j f q₂ cs e := by
  rcases h with ⟨w, u₁, hp, he⟩ | ⟨s, t, hp, hdv, he⟩
  · simp only [callMoves, List.cons_append] at hp
    cases hp with
    | cons t₁ hp =>
      cases hp with
      | cons t₂ hp => exact ⟨_, _, t₁, t₂, .inl ⟨w, u₁, hp, he⟩⟩
  · simp only [callMoves] at hp
    cases hp with
    | cons t₁ hp =>
      cases hp with
      | cons t₂ hp => exact ⟨_, _, t₁, t₂, .inr ⟨s, t, hp, hdv, he⟩⟩

theorem roundEnd_nil {x : I.HState} {e : End (Store Nat) (Payload ⊕ PUnit.{1})}
    (h : RoundEnd o I b j f x [] e) :
    (∃ (w : I.F.Ar f) (u₁ : Store Nat), I.Trans (profile o) x (.inr (.ans f w)) (.idle u₁) ∧
      e = .ret (ExpSpec.sumAns (b.liftAns j w)) u₁) ∨
    (∃ (s : Store Nat) (t : STh), x = .running f s t ∧ Linked2.DivB (profile o) s t ∧
      e = .div) := by
  rcases h with ⟨w, u₁, hp, he⟩ | ⟨s, t, hp, hdv, he⟩
  · cases hp with
    | cons t₁ hp =>
      cases hp
      exact .inl ⟨w, u₁, t₁, he⟩
  · cases hp
    exact .inr ⟨s, t, rfl, hdv, he⟩

theorem roundEnd_nil_not_ask {x q : I.HState} {m : I.E.Op}
    {e : End (Store Nat) (Payload ⊕ PUnit.{1})} (h : RoundEnd o I b j f x [] e)
    (t : I.Trans (profile o) x (.inl (.ask m)) q) : False := by
  rcases roundEnd_nil h with ⟨w, u₁, t', -⟩ | ⟨s, t₀, rfl, hdv, -⟩
  · have := (pmove_eq t' t trivial).1
    simp at this
  · exact not_trans_of_divB hdv t

theorem roundEnd_nil_eq {x : I.HState} {e e' : End (Store Nat) (Payload ⊕ PUnit.{1})}
    (h : RoundEnd o I b j f x [] e) (h' : RoundEnd o I b j f x [] e') : e = e' := by
  rcases roundEnd_nil h with ⟨w, u₁, t, rfl⟩ | ⟨s, t₀, rfl, hdv, rfl⟩
  · rcases roundEnd_nil h' with ⟨w', u₁', t', rfl⟩ | ⟨s', t₀', hx, hdv', rfl⟩
    · obtain ⟨hm, hq⟩ := pmove_eq t t' trivial
      simp only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at hm
      subst hm
      cases hq
      rfl
    · subst hx
      exact (not_trans_of_divB hdv' t).elim
  · rcases roundEnd_nil h' with ⟨w', u₁', t', -⟩ | ⟨-, -, -, -, rfl⟩
    · exact (not_trans_of_divB hdv t').elim
    · rfl

/-- **Two finished rounds from the same state agree** while their wired answers agree
(`profile o`). -/
theorem agree_end {cs : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List b.ICall)}
    (hr : List.Forall₂ (RImpRel b I) cs dss) :
    ∀ {x : I.HState} {cs' : List (Σ e : I.E.Op, I.E.Ar e)} {dss' : List (List b.ICall)}
      {e e' : End (Store Nat) (Payload ⊕ PUnit.{1})}, List.Forall₂ (RImpRel b I) cs' dss' →
      RoundEnd o I b j f x cs e → RoundEnd o I b j f x cs' e' →
      AFun.Agree (b.wireLog wire dss.flatten) e (b.wireLog wire dss'.flatten) e' := by
  induction hr with
  | nil =>
    intro x cs' dss' e e' hr' h h'
    cases hr' with
    | nil =>
      simp only [List.flatten_nil, SimpleI.wireLog, List.map_nil, AFun.Agree]
      exact roundEnd_nil_eq h h'
    | @cons c' ds' cs' dss' _ _ =>
      obtain ⟨m', n'⟩ := c'
      obtain ⟨_, _, t₁, -, -⟩ := roundEnd_cons h'
      exact (roundEnd_nil_not_ask h t₁).elim
  | @cons c ds cs dss hx hr ih =>
    intro x cs' dss' e e' hr' h h'
    obtain ⟨m, n⟩ := c
    cases hr' with
    | nil =>
      obtain ⟨_, _, t₁, -, -⟩ := roundEnd_cons h
      exact (roundEnd_nil_not_ask h' t₁).elim
    | @cons c' ds' cs' dss' hx' hr' =>
      obtain ⟨m', n'⟩ := c'
      obtain ⟨q₁, q₂, t₁, t₂, hq₂⟩ := roundEnd_cons h
      obtain ⟨q₁', q₂', t₁', t₂', hq₂'⟩ := roundEnd_cons h'
      obtain ⟨hm, rfl⟩ := pmove_eq t₁ t₁' trivial
      simp only [Sum.inl.injEq, Ev.ask.injEq] at hm
      subst hm
      rcases impRel_agree hx hx' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨z, z', rfl, rfl, hzq, hzn⟩
      · have := ScalarInstance.Trans.functional t₂ t₂'
        subst this
        show AFun.Agree (b.wireLog wire dss.flatten) _ (b.wireLog wire dss'.flatten) _
        exact ih hr' hq₂ hq₂'
      · show AFun.Agree (b.wireCall wire z :: b.wireLog wire dss.flatten) _
          (b.wireCall wire z' :: b.wireLog wire dss'.flatten) _
        refine agree_cons (by simp [hzq]) (fun hn => ?_)
        have hR : z.2 = z'.2 := sumAns_inj (eq_of_heq hn)
        have := hzn hR
        subst this
        have := ScalarInstance.Trans.functional t₂ t₂'
        subst this
        exact ih hr' hq₂ hq₂'

/-- A finished typed round of the importer's triple, after its question. -/
theorem roundEnd_of_fin {u : Store Nat} {cs : List (Σ e : I.E.Op, I.E.Ar e)}
    {e : End (Store Nat) (Payload ⊕ PUnit.{1})}
    (hd : (∃ (w : I.F.Ar f) (u₁ : Store Nat),
          I.Path (profile o) (.idle u) (.inr (.ask f) :: callMoves cs ++ [.inr (.ans f w)])
            (.idle u₁) ∧ e = .ret (ExpSpec.sumAns (b.liftAns j w)) u₁) ∨
        (∃ (s : Store Nat) (t : STh),
          I.Path (profile o) (.idle u) (.inr (.ask f) :: callMoves cs) (.running f s t) ∧
          Linked2.DivB (profile o) s t ∧ e = .div)) :
    RoundEnd o I b j f (.running f u (I.initThread f)) cs e := by
  rcases hd with ⟨w, u₁, hp, he⟩ | ⟨s, t, hp, hdv, he⟩
  · rw [List.cons_append] at hp
    cases hp with
    | cons t₁ hp =>
      cases t₁
      exact .inl ⟨w, u₁, hp, he⟩
  · cases hp with
    | cons t₁ hp =>
      cases t₁
      exact .inr ⟨s, t, hp, hdv, he⟩

/-- **The importer's triple is deterministic given answers** (`profile o`). -/
theorem det_impTripleS : AFun.Det (b.impTripleS (profile o) wire I).1 := by
  rintro u q ⟨c, en⟩ ⟨c', en'⟩ hx hy
  rcases hx with ⟨hnt, hx⟩ | ⟨j, vs, f, cs, dss, rfl, hlow, hlog, hd⟩
  · rcases hy with ⟨-, hy⟩ | ⟨j', vs', f', cs', dss', hq', hlow', -, -⟩
    · simp only [Prod.mk.injEq] at hx hy
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨rfl, rfl⟩ := hy
      simp [AFun.Agree]
    · exact (hnt (hq' ▸ typedQ_of_lowered hlow')).elim
  · rcases hy with ⟨hnt', -⟩ | ⟨j', vs', f', cs', dss', hq', hlow', hlog', hd'⟩
    · exact (hnt' (typedQ_of_lowered hlow)).elim
    simp only [Prod.mk.injEq, Payload.vals.injEq] at hq'
    obtain ⟨hj, rfl⟩ := hq'
    obtain rfl : j = j' := Fin.ext hj
    have hf : f = f' := by
      obtain ⟨xs, hc, hf1, hf2, -⟩ := hlow
      obtain ⟨xs', hc', hf1', hf2', -⟩ := hlow'
      rw [hc] at hc'
      cases hc'
      exact op_ext (hf1.trans hf1'.symm) (hf2.trans hf2'.symm)
    subst hf
    simp only at hlog hlog' hd hd'
    subst hlog hlog'
    exact agree_end (lowered_forall₂ hlow) (lowered_forall₂ hlow') (roundEnd_of_fin hd)
      (roundEnd_of_fin hd')

/-! ## The exporter's triple -/

variable {P : Profile} {e : ExpSpec}

open Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession (mem_sessFin ret_mem_typed
  ret_mem_untyped)

/-- **Deterministic exporters have deterministic returns.** -/
theorem retDet_sessTripleS (hd : e.Det P) : SessionCat.RetDet (e.sessTripleS P) := by
  intro s q c c' r r' s₁ s₁' h h'
  by_cases hq : e.TypedQ q
  · obtain ⟨rfl, R, hs, rfl⟩ := (ret_mem_typed hq).mp h
    obtain ⟨rfl, R', hs', rfl⟩ := (ret_mem_typed hq).mp h'
    obtain ⟨rfl, rfl⟩ := hd hs hs'
    simp [AFun.Agree]
  · obtain ⟨rfl, rfl, rfl⟩ := (ret_mem_untyped hq).mp h
    obtain ⟨rfl, rfl, rfl⟩ := (ret_mem_untyped hq).mp h'
    simp [AFun.Agree]

/-- **The exporter's triple is deterministic given answers iff `TDet` and `DivExcl`.** -/
theorem afunDet_sessTripleS_iff : AFun.Det (e.sessTripleS P).1 ↔ e.TDet P ∧ e.DivExcl P := by
  constructor
  · intro hD
    refine ⟨fun s s₁ s₂ q a₁ a₂ hq h₁ h₂ => ?_, fun s s' q R hq hdv hst => ?_⟩
    · have := hD s q ([], .ret (ExpSpec.sumAns a₁) s₁) ([], .ret (ExpSpec.sumAns a₂) s₂)
        (mem_sessFin.mpr ⟨rfl, .inr ⟨hq, .inl ⟨a₁, s₁, h₁, rfl⟩⟩⟩)
        (mem_sessFin.mpr ⟨rfl, .inr ⟨hq, .inl ⟨a₂, s₂, h₂, rfl⟩⟩⟩)
      simp only [AFun.Agree, End.ret.injEq] at this
      exact ⟨sumAns_inj this.1, this.2⟩
    · have := hD s q ([], .div) ([], .ret (ExpSpec.sumAns R) s')
        (mem_sessFin.mpr ⟨rfl, .inr ⟨hq, .inr ⟨hdv, rfl⟩⟩⟩)
        (mem_sessFin.mpr ⟨rfl, .inr ⟨hq, .inl ⟨R, s', hst, rfl⟩⟩⟩)
      simp [AFun.Agree] at this
  · rintro ⟨hT, hX⟩ s q ⟨c, en⟩ ⟨c', en'⟩ hx hy
    obtain ⟨hc, hx'⟩ := mem_sessFin.mp hx
    obtain ⟨hc', hy'⟩ := mem_sessFin.mp hy
    clear hx hy
    simp only at hc hc' hx' hy'
    subst hc hc'
    show en = en'
    rcases hx' with ⟨hn, h1⟩ | ⟨hq, ⟨R, s₁, hs, h1⟩ | ⟨hdv, h1⟩⟩
    · rcases hy' with ⟨-, h2⟩ | ⟨hq', -⟩
      · rw [h1, h2]
      · exact (hn hq').elim
    · rcases hy' with ⟨hn', -⟩ | ⟨-, ⟨R', s₁', hs', h2⟩ | ⟨hdv', -⟩⟩
      · exact (hn' hq).elim
      · obtain ⟨rfl, rfl⟩ := hT hq hs hs'
        rw [h1, h2]
      · exact (hX hq hdv' hs).elim
    · rcases hy' with ⟨hn', -⟩ | ⟨-, ⟨R', s₁', hs', -⟩ | ⟨-, h2⟩⟩
      · exact (hn' hq).elim
      · exact (hX hq hdv hs').elim
      · rw [h1, h2]

/-! ## The counterexample -/

theorem cexExp_det (P : Profile) : cexExp.Det P :=
  fun _ s₁ s₂ _ _ _ h₁ h₂ => ⟨h₁.trans h₂.symm, Subsingleton.elim (α := PUnit) s₁ s₂⟩

theorem cexExp_typedQ : cexExp.TypedQ (0, .vals []) :=
  ⟨⟨0, by simp [cexExp, Comp.exports]⟩, [], rfl, by simp [cexExp, Comp.exports]; rfl⟩

theorem cexExp_not_det (P : Profile) : ¬ AFun.Det (cexExp.sessTripleS P).1 := fun hD =>
  (afunDet_sessTripleS_iff.mp hD).2 (s := PUnit.unit) (s' := PUnit.unit) (R := none)
    cexExp_typedQ trivial rfl

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp
