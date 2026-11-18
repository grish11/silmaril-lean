module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.Prod
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.Fwd
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.Back

/-!
# Infinite plays of `HLinked2`: assembly

* `hlinked2_refSessProd_iff`: productive executions (infinitely many terminating calls) are the
  infinite specification sessions with the same host-state stream (`Prod`);
* `hlinked2_sessHProds_eq_refHProds`: the host-chatter plays of the reference machine are those of
  the specification (`linkHProd_fwd`, `linkHProd_inv`, after the session prefix `sessH_fwd`,
  `sessH_inv`);
* `hlinked2_refSessEquivFull_iff`: the full reference equivalence is `RefSessEquivH` with the same
  specification divergences, infinite sessions and host-chatter plays.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.HostWrite
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "RVal" => Silmaril.Wasm.Component.Reference.Val
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {prof : ProfileKind}

/-! ## Infinitely many terminating calls -/

theorem hlinked2_refSessProd_iff (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true)
    (hst : ℕ → σ × List HLinked2.HostEvent) :
    HLinked2.RefSessProd P prof l g s₀ a out hst ↔
      hst 0 = (s₀, []) ∧ ∃ Ie Ii : Silmaril.Wasm.Game.ScalarInstance,
        l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
        HLinked2.SpecSessProd P l Ie Ii (HLinked2.logG g) a out hst :=
  ⟨hlinked2_spec_of_refSessProd P prof hl g hT s₀ a out ht hst,
    fun ⟨h0, _, _, hIe, hIi, h⟩ =>
      hlinked2_refSessProd_of_spec P prof hl g hT s₀ hIe hIi a out hst h0 h⟩

/-! ## Host chatter -/

section Log

variable {σ : Type} {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

theorem hostAnswers_log_prefix {n : Nat} {s s' : σ × List HLinked2.HostEvent}
    {d : Σ _ : (sigN n).Op, Option Payload} (h : HostAnswersS (HLinked2.logG g) s d s') :
    s.2 <+: s'.2 := by
  obtain ⟨k, ws, -, hm⟩ := h
  rcases d with ⟨q, R⟩
  rcases R with _ | p
  · obtain ⟨-, rfl⟩ := hm
    exact List.prefix_refl _
  · cases p with
    | vals us =>
      simp only [HLinked2.logG, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨rs', t'⟩, -, -, rfl⟩ := hm
      exact List.prefix_append _ _
    | flat _ => exact hm.elim

theorem hostRun_log_prefix {n : Nat} {s s' : σ × List HLinked2.HostEvent}
    {ds : List (Σ _ : (sigN n).Op, Option Payload)} (h : HostRun (HLinked2.logG g) s ds s') :
    s.2 <+: s'.2 := by
  induction h with
  | nil => exact List.prefix_refl _
  | cons ha _ ih => exact (hostAnswers_log_prefix ha).trans ih

/-- Under the logging host, a stream of host states with unbounded logs, each step a `HostRun`,
changes infinitely often. -/
theorem hst_changes {n : Nat} {hst : ℕ → σ × List HLinked2.HostEvent}
    {ds : ℕ → List (Σ _ : (sigN n).Op, Option Payload)}
    (hr : ∀ k, HostRun (HLinked2.logG g) (hst k) (ds k) (hst (k + 1)))
    (hunb : ∀ M, ∃ k, M ≤ (hst k).2.length) : ∀ N, ∃ i, N ≤ i ∧ hst i ≠ hst (i + 1) := by
  intro N
  by_contra hc'
  have hc : ∀ i, N ≤ i → hst i = hst (i + 1) := fun i hi =>
    Classical.byContradiction fun hne => hc' ⟨i, hi, hne⟩
  have hconst : ∀ d, hst (N + d) = hst N := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => rw [← Nat.add_assoc, ← hc (N + d) (Nat.le_add_right _ _), ih]
  have hpre : ∀ d k, (hst k).2 <+: (hst (k + d)).2 := by
    intro d
    induction d with
    | zero => exact fun k => List.prefix_refl _
    | succ d ih => exact fun k => (ih k).trans (hostRun_log_prefix (hr (k + d)))
  obtain ⟨k, hk⟩ := hunb ((hst N).2.length + 1)
  rcases le_total k N with hle | hle
  · have := (hpre (N - k) k).length_le
    rw [Nat.add_sub_cancel' hle] at this
    omega
  · have := hconst (k - N)
    rw [Nat.add_sub_cancel' hle] at this
    rw [this] at hk
    omega

end Log

/-- **The host-chatter plays of the specification are those of the reference machine.** -/
theorem hlinked2_sessHProds_sub (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) :
    HLinked2.sessHProds P l g s₀ calls j vs ⊆ HLinked2.refHProds P prof l g s₀ calls j vs := by
  rintro ⟨outs, st, ev⟩ ⟨Ie, Ii, hs, u, π, hst, hIe, hIi, hspec, hhr, hround, hlog⟩
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (answerHostS P (HLinked2.logG g)) (s₀, []) hIe hIi
  obtain ⟨cs', ιe', ιi', G', ST', hsr, R'⟩ := sessH_fwd (prof := prof)
    (impl := answerImplS (HLinked2.logG g))
    (handles_answer hl.impArity hl.impFloatFree hl.wireTy) (HostTyped.logG hT) S₀ rfl hfs hspec
    _ _ _ _ [] (s₀, []) 0 st R₀ hhr
  rw [Nat.zero_add] at R'
  obtain ⟨_f, _xs, _q, _c, ds, _πs, _h₁, _h₂, _h₃, _h₄, _h₅, _h₆, hc⟩ := id hround
  have hstep : ∀ k, HostRun (HLinked2.logG g) (hst k) (l.hostCalls (ds k)) (hst (k + 1)) :=
    fun k => (hc k).2.2.2
  have hunb : ∀ M, ∃ k, M ≤ (hst k).2.length := by
    intro M
    obtain ⟨n, k, hn, hk⟩ := hlog M
    exact ⟨k, by rw [hk, List.length_append, length_streamTake]; omega⟩
  obtain ⟨t, s, ht, hcov, -⟩ := linkHProd_fwd (prof := prof)
    (impl := answerImplS (HLinked2.logG g)) (ST := ST')
    (handles_answer hl.impArity hl.impFloatFree hl.wireTy) (HostTyped.logG hT) S₀ rfl hfs R'
    hround (hst_changes hstep hunb)
  refine ⟨_, ⟨0⟩, l.exportMap,
    calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId), _, _, hmem,
    mapM_lookupH hl.impGood calls, exportMapH_lookup hl.impGood j, ?_, rfl, t, s, ht, ?_⟩
  · rw [zip_callArgsH]
    exact hsr
  · intro N
    obtain ⟨n, k, hn, hk⟩ := hlog N
    obtain ⟨p, hp⟩ := hcov k
    exact ⟨n, p, hn, by rw [hp, hk]; rfl⟩

/-- **The host-chatter plays of the reference machine are those of the specification**, for
typed calls. -/
theorem hlinked2_refHProds_sub (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    HLinked2.refHProds P prof l g s₀ calls j vs ⊆ HLinked2.sessHProds P l g s₀ calls j vs := by
  rintro ⟨outs, st, ev⟩ ⟨m₀, inst, es, fs', m₁, f, hr, hfs', hf, hSq, hst, hd⟩
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := P) hl.expGood hl.expInst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (answerHostS P (HLinked2.logG g)) (s₀, []) hFe.isInst hIi
  obtain ⟨mU, -, -, -, huniq⟩ :=
    hlinked2_instantiates P prof hl (answerHostS P (HLinked2.logG g)) (s₀, [])
  have hsafe₁ : CfgSafe logExt m₁ := HLinked2.logSession_cfgSafe hr hSq
  have h₁ := huniq _ hmem
  have h₂ := huniq _ hr
  simp only [InstResult.instance.injEq] at h₁ h₂
  obtain ⟨rfl, rfl, rfl⟩ := h₂
  rw [← h₁.1] at hSq
  have hfs'' : fs' = calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs'.symm.trans (mapM_lookupH hl.impGood calls))
  subst hfs''
  have hf' : f = ⟨l.host.length + l.exp.exports.length + j⟩ :=
    Option.some.inj (hf.symm.trans (exportMapH_lookup hl.impGood j))
  subst hf'
  rw [zip_callArgsH] at hSq
  obtain ⟨outs', hs, u', π', hspec, hhr, ho', cs', ιe', ιi', G', ST', hmE, R'⟩ :=
    sessH_inv (prof := prof) (impl := answerImplS (HLinked2.logG g))
      (handlesB_answer hl.impArity hl.impFloatFree hl.wireTy) (HostTyped.logG hT) S₀
      rfl hfs calls _ _ _ _ _ (s₀, []) _ _ 0 _ m₁ R₀ ht hSq
  rw [Nat.zero_add] at R'
  rw [hmE] at hd hsafe₁
  obtain ⟨hstr, hround, hlog⟩ := linkHProd_inv (prof := prof) hT S₀ rfl hfs R' hsafe₁ j hvs hd
  obtain rfl := SessionAdequacy.refOuts_inj ho'
  subst hst
  exact ⟨Ie, Ii, hs, u', π', hstr, hFe.isInst, hIi, hspec, hhr, hround, hlog⟩

/-- **The host-chatter plays of a linked component with host imports are those of the reference
machine**, for typed calls. -/
theorem hlinked2_sessHProds_eq_refHProds (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    HLinked2.sessHProds P l g s₀ calls j vs = HLinked2.refHProds P prof l g s₀ calls j vs :=
  Set.Subset.antisymm (hlinked2_sessHProds_sub P prof hl g hT s₀ calls j vs)
    (hlinked2_refHProds_sub P prof hl g hT s₀ calls j vs ht hvs)

/-! ## The full equivalence -/

/-- The specification side of a productive execution. -/
def SpecProd (P : Profile) (l : HLinked2) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (hst : ℕ → σ × List HLinked2.HostEvent) : Prop :=
  hst 0 = (s₀, []) ∧ ∃ Ie Ii : Silmaril.Wasm.Game.ScalarInstance,
    l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
    HLinked2.SpecSessProd P l Ie Ii (HLinked2.logG g) a out hst

theorem typed_castStreamH {l l' : HLinked2} (h : HLinked2.RefSessEquivH P prof l l')
    {a : ℕ → Fin l.imp.exports.length × List IVal}
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) :
    ∀ k, ValTy.checkList
      l'.imp.exports[(Linked2.castStream (l := l.toL2) (l' := l'.toL2) h.len a k).1].ty.params
      (Linked2.castStream (l := l.toL2) (l' := l'.toL2) h.len a k).2 = true := fun k => by
  show ValTy.checkList l'.imp.exports[Fin.cast h.len (a k).1].ty.params (a k).2 = true
  rw [h.ty]
  exact ht k

/-- **The full equivalence on the specification**: for adequate linked components with host
imports, the reference-defined full equivalence is `RefSessEquivH` with the same specification
divergences, the same infinite specification sessions and the same specification host-chatter
plays, under every typed host. -/
theorem hlinked2_refSessEquivFull_iff {l l' : HLinked2} (hl : l.Adequate) (hl' : l'.Adequate) :
    HLinked2.RefSessEquivFull P prof l l' ↔ ∃ h : HLinked2.RefSessEquivH P prof l l',
      (∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
        (vs : List IVal), SimpleI.TypedCalls l.imp calls →
        ValTy.checkList l.imp.exports[j].ty.params vs = true →
        ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
          ∀ s₀ : σ, HLinked2.sessDivs P l g s₀ calls j vs =
              HLinked2.sessDivs P l' g s₀
                (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len calls)
                (Fin.cast h.len j) vs ∧
            HLinked2.sessHProds P l g s₀ calls j vs =
              HLinked2.sessHProds P l' g s₀
                (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len calls)
                (Fin.cast h.len j) vs) ∧
      ∀ (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
        (∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) →
        ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
          ∀ (s₀ : σ) (hst : ℕ → σ × List HLinked2.HostEvent),
            (SpecProd P l g s₀ a out hst ↔
              SpecProd P l' g s₀ (Linked2.castStream (l := l.toL2) (l' := l'.toL2) h.len a)
                out hst) := by
  have keyH : ∀ (h : HLinked2.RefSessEquivH P prof l l')
      (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
      (vs : List IVal), SimpleI.TypedCalls l.imp calls →
      ValTy.checkList l.imp.exports[j].ty.params vs = true →
      ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
        ∀ s₀ : σ,
        (HLinked2.sessHProds P l g s₀ calls j vs =
            HLinked2.sessHProds P l' g s₀ (Linked2.castCalls (l := l.toL2) (l' := l'.toL2)
              h.len calls) (Fin.cast h.len j) vs ↔
          HLinked2.refHProds P prof l g s₀ calls j vs =
            HLinked2.refHProds P prof l' g s₀ (Linked2.castCalls (l := l.toL2) (l' := l'.toL2)
              h.len calls) (Fin.cast h.len j) vs) := by
    intro h calls j vs ht hvs σ g hT s₀
    have hvs' : ValTy.checkList l'.imp.exports[Fin.cast h.len j].ty.params vs = true := by
      rw [h.ty j]
      exact hvs
    rw [hlinked2_sessHProds_eq_refHProds P prof hl g hT s₀ calls j vs ht hvs,
      hlinked2_sessHProds_eq_refHProds P prof hl' g (hostTyped_congr h.host hT) s₀ _ _ vs
        (typedCalls_castH h ht) hvs']
  have keyP : ∀ (h : HLinked2.RefSessEquivH P prof l l')
      (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
      (∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) →
      ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
        ∀ (s₀ : σ) (hst : ℕ → σ × List HLinked2.HostEvent),
        ((SpecProd P l g s₀ a out hst ↔
            SpecProd P l' g s₀ (Linked2.castStream (l := l.toL2) (l' := l'.toL2) h.len a) out
              hst) ↔
          (HLinked2.RefSessProd P prof l g s₀ a out hst ↔
            HLinked2.RefSessProd P prof l' g s₀
              (Linked2.castStream (l := l.toL2) (l' := l'.toL2) h.len a) out hst)) := by
    intro h a out ht σ g hT s₀ hst
    rw [hlinked2_refSessProd_iff P prof hl g hT s₀ a out ht hst,
      hlinked2_refSessProd_iff P prof hl' g (hostTyped_congr h.host hT) s₀ _ out
        (typed_castStreamH h ht) hst]
    rfl
  constructor
  · intro h
    obtain ⟨hD, hdiv⟩ := (hlinked2_refSessEquivD_iff (prof := prof) hl hl').mp h.toRefSessEquivD
    refine ⟨hD, fun calls j vs ht hvs σ g hT s₀ => ⟨hdiv calls j vs ht hvs g hT s₀, ?_⟩,
      fun a out ht σ g hT s₀ hst => (keyP hD a out ht g hT s₀ hst).mpr
        (h.prod a out ht g hT s₀ hst)⟩
    exact (keyH hD calls j vs ht hvs g hT s₀).mpr (h.hprod calls j vs ht hvs g hT s₀)
  · rintro ⟨hD, hdh, hp⟩
    have hRD := (hlinked2_refSessEquivD_iff (prof := prof) hl hl').mpr
      ⟨hD, fun calls j vs ht hvs σ g hT s₀ => (hdh calls j vs ht hvs g hT s₀).1⟩
    exact ⟨hRD, fun a out ht σ g hT s₀ hst => (keyP hD a out ht g hT s₀ hst).mp
        (hp a out ht g hT s₀ hst),
      fun calls j vs ht hvs σ g hT s₀ => (keyH hD calls j vs ht hvs g hT s₀).mp
        (hdh calls j vs ht hvs g hT s₀).2⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf
