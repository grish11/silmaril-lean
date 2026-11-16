module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.IR
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.GamesInv
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Linked

/-!
# Linked components with host imports: IR to specification

`hlinked2_irToSpec`: the typed session plays of `l.toComp.den (impSem P)` (`HLinked2.sessMoves`,
the host calls of each round visible lower moves) are read back into an `HLinked2.SessSpec`
session from the instances' stores, with the same host calls. #724's read-back of `Linked2`
(`LinkedSessionAdeq.Linked`), with the layers that host imports add. From the top:

* `atSizes` (`hc_narrowH_inv`, `hrounds_widenH_inv`): the host calls of a round, as lower
  calls of `sigN host.length`, are the lower calls of the round at the untyped interface;
* the linked export handler (`hc_exportsH_inv`): export `j` is question `k + n_A + j` of the
  environment (`k = host.length`);
* the second environment over the first (`serveC_inv`): rounds of the importer's side whose
  lower calls are served by rounds of the first environment, whose own lower calls are the
  visible ones;
* `splitH`, the pairing and the importer's node, then the importer's IR (`hc_splitH_inv`,
  `cplay_of_pair_inr`, `hb_inv`, `imp_readback`), unchanged from `Linked2`; the importer's node
  renames its import calls (`hrounds_impl_inv`, the converse of `hrounds_impl`);
* the first environment (`env1_inv`): through the mask, `splitH` and the pairing of copycat
  with the exporter's node, a host call is answered by the same call below (copycat, `id_cs`),
  a wired call by a round of the exporter without lower calls (`cs_nil_of_noInl`);
* the exporter (`expNodeH_specRoundsT`, `expRunH_of_sessRounds`): its rounds are #676's
  read-back, a session of the exporter on the wired calls, which with the host calls passed
  through is an `ExpRunH`;
* the session (`sessSpecH_of`): the instance's play and the `ExpRunH` split round by round.

**The host answers are unconstrained.** A host call is answered by copycat with whatever the
lower interface answers, and `ExpRunH` lets a host call have any answer: every IR play is read
back, whatever its host answers.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {l : HLinked2}

/-! ## `atSizes` and the export handler -/

/-- A round of an interface of `n` functions, at the untyped interface. -/
def narrowC {E : Sig.{0}} {n : Nat} (r : CRound E (sigN n)) : CRound E sigU :=
  ⟨(r.q.1.val, r.q.2), r.cs, r.a⟩

/-- A round shifted up by `e`. -/
def shiftC {E : Sig.{0}} (e : Nat) (r : CRound E sigU) : CRound E sigU :=
  ⟨(e + r.q.1, r.q.2), r.cs, r.a⟩

/-- `narrowH` forwards each round (`cplay_comp_ofHandler` at `narrowH`, in reverse). -/
theorem hc_narrowH_inv {E : Sig.{0}} {n : Nat} :
    ∀ {up : List (CRound E (sigN n))} {low : List (CRound E sigU)}, HC (narrowH n) up low →
      low = up.map narrowC
  | _, _, .nil => rfl
  | _, _, .pure hq _ => by simp [narrowH] at hq
  | _, _, .call hq hk H => by
    simp only [narrowH, Prog.call.injEq] at hq
    obtain ⟨rfl, hk'⟩ := hq
    cases eq_of_heq hk'
    cases hk
    rw [hc_narrowH_inv H]
    rfl

/-- `widenH` forwards the lower calls of a round of `sigN n` (`hrounds_widenH` in reverse). -/
theorem hrounds_widenH_inv {n : Nat} :
    ∀ {Y Z : List (Round (sigN n))}, HRounds (widenH n) (Y.map Round.forget) Z → Z = Y
  | [], _, H => by cases H; rfl
  | ⟨(i, p), a⟩ :: Y, Z, H => by
    have hw : widenH n (i.val, p) = .call (i, p) fun r => .pure r := dite_eq_left i.isLt
    rcases hrounds_cons_inv (show HRounds (widenH n) (⟨(i.val, p), a⟩ :: Y.map Round.forget) Z
      from H) with ⟨hq, -⟩ | ⟨q', k, a', low', rfl, hq, hk, H'⟩
    · rw [hw] at hq
      cases hq
    · rw [hw] at hq
      cases hq
      cases hk
      rw [hrounds_widenH_inv H']

/-- The linked export handler forwards export `j` to question `k + n_A + j` of the
environment. -/
theorem hc_exportsH_inv {E : Sig.{0}} (l : HLinked2) :
    ∀ {up low : List (CRound E sigU)},
      HC (exportsH (l.host.length + l.exp.exports.length + l.imp.exports.length)
        l.toComp.exports) up low →
      (∀ r ∈ up, r.q.1 < l.imp.exports.length) →
      low = up.map (shiftC (l.host.length + l.exp.exports.length))
  | _, _, .nil, _ => rfl
  | _, _, .pure (q := q) hq _, hlt => by
    have e := hq.symm.trans (exportsH_toCompH l (hlt _ List.mem_cons_self) q.2)
    cases e
  | _, _, .call (q := q) hq hk H, hlt => by
    have e := hq.symm.trans (exportsH_toCompH l (hlt _ List.mem_cons_self) q.2)
    cases e
    cases hk
    rw [hc_exportsH_inv l H fun r hr => hlt r (List.mem_cons_of_mem _ hr)]
    rfl

/-! ## The importer's import calls -/

/-- An import call of the importer, as the specification reads it: a wired call on values of
the wired export's parameter types, or a host call. -/
def WTH (l : HLinked2) (y : Round (sigN l.imp.imports.length)) : Prop :=
  (∃ (w : Fin l.exp.exports.length) (ws : List IVal), l.wire[y.1.1.val]? = some w.val ∧
    y.1.2 = .vals ws ∧ ValTy.checkList l.exp.exports[w].ty.params ws = true) ∨
  (l.wire.length ≤ y.1.1.val ∧ y.1.1.val - l.wire.length < l.host.length)

theorem wth_of (hw : l.WireTy) {y : Round (sigN l.imp.imports.length)} {nm : String}
    {ft : FuncTy} {ws : List IVal} (hft : l.imp.imports[y.1.1.val]? = some (nm, ft))
    (hp : y.1.2 = .vals ws) (hck : ValTy.checkList ft.params ws = true) : WTH l y := by
  by_cases h : y.1.1.val < l.wire.length
  · obtain ⟨x, hx, hty⟩ := hw.ty _ _ (List.getElem?_eq_getElem h)
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hx
    rw [hft] at hty
    have hft' : ft = x.ty := by simpa using hty
    refine .inl ⟨⟨_, hlt⟩, ws, List.getElem?_eq_getElem h, hp, ?_⟩
    have hx' : l.exp.exports[(⟨_, hlt⟩ : Fin l.exp.exports.length)] = x := hget
    rw [hx', ← hft']
    exact hck
  · have hlen := congrArg List.length hw.shape.1
    rw [List.length_drop] at hlen
    have hy := y.1.1.isLt
    exact .inr ⟨by omega, by omega⟩

theorem cls_of_wth {y : Round (sigN l.imp.imports.length)} : WTH l y → Cls l y
  | .inl ⟨w, _, hw, _, _⟩ =>
    .inl ⟨(List.getElem?_eq_some_iff.mp hw).1, by rw [getD_of_wire hw]; exact w.isLt⟩
  | .inr h => .inr h

/-- The importer's node renames its import calls (`hrounds_impl` in reverse). -/
theorem hrounds_impl_inv :
    ∀ {ds : List (Round (sigN l.imp.imports.length))} {cs' : List (Round sigU)},
      (∀ x ∈ ds, Cls l x) →
      HRounds (implsH (l.host.length + l.exp.exports.length) (l.wireArgs ++ l.hostArgs))
        (ds.map Round.forget) cs' → cs' = ds.map (rn l)
  | [], _, _, H => by cases H; rfl
  | x :: ds, cs', hc, H => by
    have H' : HRounds (implsH (l.host.length + l.exp.exports.length) (l.wireArgs ++ l.hostArgs))
        (⟨(x.1.1.val, x.1.2), x.2⟩ :: ds.map Round.forget) cs' := H
    have hx := implsH_args (hc x List.mem_cons_self)
    rcases hrounds_cons_inv H' with ⟨hq, -⟩ | ⟨q', k, a', low', rfl, hq, hk, H''⟩
    · rw [hx] at hq
      cases hq
    · rw [hx] at hq
      cases hq
      cases hk
      rw [hrounds_impl_inv (fun y hy => hc y (List.mem_cons_of_mem _ hy)) H'', List.map_cons]
      exact congrArg (· :: ds.map (rn l)) (Sigma.ext rfl (heq_of_eq (rn_snd x).symm))

/-! ## The first environment -/

/-- The lower calls of a round of the first environment: the round itself for a host call
(`q < k`), none otherwise. -/
def csOf (k : Nat) (r : Round sigU) : List (Round sigU) := if r.1.1 < k then [r] else []

/-- A round of the first environment as a round of the exporter (`none` for a host call). -/
def eOf (k : Nat) (r : Round sigU) : Option (Round sigU) :=
  if r.1.1 < k then none else some ⟨(r.1.1 - k, r.1.2), r.2⟩

/-- A round below `splitH k`, as a round of copycat or of the exporter's node. -/
def mU (k : Nat) (u : CRound sigU sigU) : CRound sigU sigU ⊕ CRound sigU sigU :=
  if u.q.1 < k then .inl u else .inr ⟨(u.q.1 - k, u.q.2), u.cs, u.a⟩

theorem hc_splitH_mU {k : Nat} :
    ∀ {U : List (CRound sigU sigU)} {D : List (CRound sigU (sigU ⊕ₛ sigU))},
      HC (splitH k) U D → D.map CRound.unlift = U.map (mU k)
  | _, _, .nil => rfl
  | _, _, .pure hq _ => by
    simp only [splitH] at hq
    split at hq <;> cases hq
  | _, _, .call (q := q) hq hk H => by
    rw [List.map_cons, List.map_cons, hc_splitH_mU H]
    simp only [splitH] at hq
    by_cases h : q.1 < k
    · rw [ite_eq_left h] at hq
      cases hq
      cases hk
      simp only [mU, h, ↓reduceIte, CRound.unlift]
    · rw [ite_eq_right h] at hq
      cases hq
      cases hk
      simp only [mU, h, ↓reduceIte, CRound.unlift]

theorem hrounds_maskH_lt {k : Nat} {q : sigU.Op} {a : Option Payload} {cs' : List (Round sigU)}
    (hlt : q.1 < k) (H : HRounds (maskH k) [⟨q, a⟩] cs') : cs' = [⟨q, a⟩] := by
  rcases hrounds_cons_inv H with ⟨hq, -⟩ | ⟨q', kk, a', low', rfl, hq, hk, H'⟩
  · have e := hq.symm.trans (maskH_lt hlt q.2)
    cases e
  · have e := hq.symm.trans (maskH_lt hlt q.2)
    cases e
    cases hk
    cases H'
    rfl

theorem toRound_of_hbr {E F G : Sig.{0}} {h : Handler E F} :
    ∀ {U : List (CRound F G)} {S : List (CRound E G)}, List.Forall₂ (HBR h) U S →
      U.map CRound.toRound = S.map CRound.toRound
  | _, _, .nil => rfl
  | _, _, .cons ⟨_, _, _, _, rfl, rfl, _⟩ t => by
    rw [List.map_cons, List.map_cons, toRound_of_hbr t]
    rfl

theorem rights_mU {k : Nat} : ∀ (U : List (CRound sigU sigU)),
    (∀ u ∈ U, ¬ u.q.1 < k → u.cs = []) →
    rights (U.map (mU k)) = ((U.map CRound.toRound).filterMap (eOf k)).map
      fun r => (⟨r.1, [], r.2⟩ : CRound sigU sigU)
  | [], _ => rfl
  | u :: U, h => by
    have h' : ∀ u ∈ U, ¬ u.q.1 < k → u.cs = [] := fun u' hu => h u' (List.mem_cons_of_mem _ hu)
    by_cases hlt : u.q.1 < k
    · have e₁ : mU k u = .inl u := ite_eq_left hlt
      have e₂ : eOf k (CRound.toRound u) = none := by
        simp only [eOf, CRound.toRound, hlt, ↓reduceIte]
      rw [List.map_cons, List.map_cons, List.filterMap_cons_none e₂, e₁]
      exact rights_mU U h'
    · have e₁ : mU k u = .inr ⟨(u.q.1 - k, u.q.2), u.cs, u.a⟩ := ite_eq_right hlt
      have e₂ : eOf k (CRound.toRound u) = some ⟨(u.q.1 - k, u.q.2), u.a⟩ := by
        simp only [eOf, CRound.toRound, hlt, ↓reduceIte]
      rw [List.map_cons, List.map_cons, List.filterMap_cons_some e₂, e₁, List.map_cons]
      show (⟨(u.q.1 - k, u.q.2), u.cs, u.a⟩ : CRound sigU sigU) :: rights (U.map (mU k)) = _
      rw [h u List.mem_cons_self hlt, rights_mU U h']

theorem forall₂_mem_right_mem {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → ∀ y ∈ b, ∃ x ∈ a, R x y
  | _, _, .nil, _, hy => nomatch hy
  | _, _, .cons h t, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, h'⟩ := forall₂_mem_right_mem t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h'⟩

/-- **The first environment read back**: each of its rounds makes the same call below for a
host call, and no call for a wired call; the wired calls are rounds of the exporter's node. -/
theorem env1_inv {S : List (CRound sigU sigU)} (h : cplay S ∈ env1 (impSem P) l) :
    (∀ s ∈ S, s.cs = csOf l.host.length (CRound.toRound s)) ∧
      twos ((S.map CRound.toRound).filterMap (eOf l.host.length)) ∈ expNodeH (impSem P) l := by
  have h' : cplay S ∈ (Strategy.ofHandler (maskH l.host.length)).comp
      (((Strategy.id sigU).pair (expNodeH (impSem P) l)).comp
        (Strategy.ofHandler (splitH l.host.length))) := h
  obtain ⟨U, HU, hU⟩ := hb_inv (oneShot_maskH _) h'
  obtain ⟨D, HD, hD⟩ := hc_inv (oneShot_splitH _) hU
  obtain ⟨hl, hr⟩ := pair_mixed_inv hD
  rw [hc_splitH_mU HD] at hl hr
  have hL := id_cs hl
  have hN : ∀ t ∈ expNodeH (impSem P) l, NoInl t :=
    noInl_comp (noInl_ofHandler_pure fun _ => ⟨none, rfl⟩)
  have hR := cs_nil_of_noInl (hN _ hr)
  have hU1 : ∀ u ∈ U, u.q.1 < l.host.length → u.cs = [⟨u.q, u.a⟩] := fun u hu hlt =>
    hL u (mem_lefts (List.mem_map.mpr ⟨u, hu, ite_eq_left hlt⟩))
  have hU2 : ∀ u ∈ U, ¬ u.q.1 < l.host.length → u.cs = [] := fun u hu hlt =>
    hR ⟨(u.q.1 - l.host.length, u.q.2), u.cs, u.a⟩
      (mem_rights (List.mem_map.mpr ⟨u, hu, ite_eq_right hlt⟩))
  have F := hb_forall₂ HU
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨u, hu, q, a, cs, cs', rfl, rfl, H⟩ := forall₂_mem_right_mem F s hs
    by_cases hlt : q.1 < l.host.length
    · have hcs : cs = [⟨q, a⟩] := hU1 _ hu hlt
      subst hcs
      rw [hrounds_maskH_lt hlt H]
      exact (ite_eq_left hlt).symm
    · have hcs : cs = [] := hU2 _ hu hlt
      subst hcs
      cases H
      exact (ite_eq_right hlt).symm
  · rw [rights_mU U hU2, cplay_nocalls, toRound_of_hbr F] at hr
    exact hr

/-! ## The exporter -/

/-- **The exporter's node read back**: complete rounds of the exporter's node are
specification rounds of the exporter from its instance's store. -/
theorem expNodeH_specRoundsT (he : l.exp.Good) {I : SInst} (hI : l.exp.mod.IsInst I)
    {L : List (Round sigU)} (h : twos L ∈ expNodeH (impSem P) l) :
    SpecRoundsT P l.exp I I.store L := by
  have hD : ∀ t ∈ l.exp.toComp.denU (modSem P), NoInl t := by
    rw [denU_toComp]
    exact noInl_comp (noInl_comp (noInl_ofHandler_pure pure_maskH0))
  have hU : ∀ t ∈ (SimpleI.ofSimple l.exp).toComp.denU (impSem P), NoInl t := by
    rw [denU_ofSimple]
    exact hD
  have h' := twos_of_comp_noInl hU h
  rw [denU_ofSimple] at h'
  exact specRoundsT_of_denU he hI h'

/-- **A session of the exporter on the typed wired calls, the host calls passed through, is an
`ExpRunH`.** -/
theorem expRunH_of_sessRounds {I : SInst} :
    ∀ {s s' : Store Nat} (ds : List (Round (sigN l.imp.imports.length))), (∀ d ∈ ds, WTH l d) →
      SessRounds P l.exp I s (ds.filterMap (aCall? l)) s' → HLinked2.ExpRunH P l I s ds s'
  | s, _, [], _, h => by
    cases h
    exact .nil s
  | _, _, ⟨(k, p), R⟩ :: ds, hwt, h => by
    have hwt' : ∀ d ∈ ds, WTH l d := fun d hd => hwt d (List.mem_cons_of_mem _ hd)
    rcases hwt _ List.mem_cons_self with ⟨w, ws, hw, hp, hck⟩ | ⟨hge, hlt⟩
    · have hp' : p = .vals ws := hp
      subst hp'
      have hk : k.val < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
      have e : aCall? l ⟨(k, .vals ws), R⟩ = some ⟨(w.val, .vals ws), R⟩ := by
        simp only [aCall?, hk, ↓reduceIte, getD_of_wire hw]
      rw [List.filterMap_cons_some e] at h
      cases h with
      | bad _ hn _ =>
        exact absurd (hn w.isLt ws rfl) (by rw [Bool.not_eq_false]; exact hck)
      | ret _ hret h' => exact .ret w hw hret (expRunH_of_sessRounds ds hwt' h')
      | trap _ htrap h' => exact .trap w hw htrap (expRunH_of_sessRounds ds hwt' h')
    · have hge' : l.wire.length ≤ k.val := hge
      have hn : ¬ k.val < l.wire.length := by omega
      have e : aCall? l ⟨(k, p), R⟩ = none := by simp only [aCall?, hn, ↓reduceIte]
      rw [List.filterMap_cons_none e] at h
      exact .host ⟨k.val - l.wire.length, hlt⟩
        (by show k.val = l.wire.length + (k.val - l.wire.length); omega)
        (expRunH_of_sessRounds ds hwt' h)

theorem expRunH_split {I : SInst} :
    ∀ {s s' : Store Nat} (ds ds' : List (Round (sigN l.imp.imports.length))),
      HLinked2.ExpRunH P l I s (ds ++ ds') s' →
      ∃ s₁, HLinked2.ExpRunH P l I s ds s₁ ∧ HLinked2.ExpRunH P l I s₁ ds' s'
  | s, _, [], _, h => ⟨s, .nil s, h⟩
  | _, _, _ :: ds, ds', h => by
    rw [List.cons_append] at h
    cases h with
    | ret w hw hret h' =>
      obtain ⟨s₁, h₁, h₂⟩ := expRunH_split ds ds' h'
      exact ⟨s₁, .ret w hw hret h₁, h₂⟩
    | trap w hw htrap h' =>
      obtain ⟨s₁, h₁, h₂⟩ := expRunH_split ds ds' h'
      exact ⟨s₁, .trap w hw htrap h₁, h₂⟩
    | host i hi h' =>
      obtain ⟨s₁, h₁, h₂⟩ := expRunH_split ds ds' h'
      exact ⟨s₁, .host i hi h₁, h₂⟩

theorem sx_wired {x : Round (sigN l.imp.imports.length)} (h : x.1.1.val < l.wire.length) :
    sx l x = ⟨(l.host.length + l.wire.getD x.1.1.val 0, x.1.2), [], x.2⟩ := by
  unfold sx
  exact ite_eq_left h

theorem sx_host {x : Round (sigN l.imp.imports.length)} (h : ¬ x.1.1.val < l.wire.length) :
    sx l x = ⟨(x.1.1.val - l.wire.length, x.1.2), [⟨(x.1.1.val - l.wire.length, x.1.2), x.2⟩],
      x.2⟩ := by
  unfold sx
  exact ite_eq_right h

theorem eOf_rn {x : Round (sigN l.imp.imports.length)} (hx : Cls l x) :
    eOf l.host.length (rn l x) = aCall? l x := by
  by_cases h : x.1.1.val < l.wire.length
  · have h₁ : ¬ (l.host.length + l.wire.getD x.1.1.val 0 < l.host.length) := by omega
    unfold rn
    rw [sx_wired h]
    simp only [aCall?, eOf, h, h₁, ↓reduceIte, Nat.add_sub_cancel_left]
  · have h₁ : x.1.1.val - l.wire.length < l.host.length := by
      rcases hx with hx | hx
      · exact absurd hx.1 h
      · exact hx.2
    unfold rn
    rw [sx_host h]
    simp only [aCall?, eOf, h, h₁, ↓reduceIte]

theorem filterMap_rn : ∀ (X : List (Round (sigN l.imp.imports.length))), (∀ x ∈ X, Cls l x) →
    (X.map (rn l)).filterMap (eOf l.host.length) = X.filterMap (aCall? l)
  | [], _ => rfl
  | x :: X, h => by
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, eOf_rn (h x List.mem_cons_self),
      filterMap_rn X fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem aCall_lt {X : List (Round (sigN l.imp.imports.length))} (h : ∀ x ∈ X, Cls l x) :
    ∀ y ∈ X.filterMap (aCall? l), y.1.1 < l.exp.exports.length := by
  intro y hy
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.mp hy
  by_cases hw : x.1.1.val < l.wire.length
  · simp only [aCall?, hw, ↓reduceIte, Option.some.injEq] at e
    subst e
    rcases h x hx with hc | hc
    · exact hc.2
    · omega
  · simp only [aCall?, hw, ↓reduceIte, reduceCtorEq] at e

/-! ## The rounds of the session -/

/-- The round of a session play: the call, its host calls and its outcome. -/
def topRH (l : HLinked2)
    (co : (Fin l.imp.exports.length × List IVal) × Option (List IVal) ×
      List (Round (sigN l.host.length))) :
    CRound (sigN l.host.length) (sigN l.toComp.exports.length) :=
  ⟨(⟨co.1.1, by simp [HLinked2.exports_length_toComp]⟩, .vals co.1.2), co.2.2, co.2.1.map .vals⟩

theorem sessMovesH_eq (l : HLinked2) :
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
      (hs : List (List (Round (sigN l.host.length)))),
      l.sessMoves calls outs hs = cplay ((calls.zip (outs.zip hs)).map (topRH l))
  | [], _, _ => rfl
  | (_, _) :: _, [], _ => rfl
  | (_, _) :: _, _ :: _, [] => rfl
  | (j, vs) :: cs, o :: os, h :: hs => by
    show _ :: (_ ++ _ :: l.sessMoves cs os hs) =
      _ :: (_ ++ _ :: cplay ((cs.zip (os.zip hs)).map (topRH l)))
    rw [sessMovesH_eq l cs os hs]
    rfl

/-- The relation of a round of the second environment to the round of the session play. -/
def RB (l : HLinked2) (r : SRound sigU sigU sigU)
    (co : (Fin l.imp.exports.length × List IVal) × Option (List IVal) ×
      List (Round (sigN l.host.length))) : Prop :=
  ∃ u, r.vis = shiftC (l.host.length + l.exp.exports.length) u ∧
    HBR (widenH l.host.length) u (narrowC (topRH l co))

/-- The relation of a round of the importer's instance to the round of the second
environment. -/
def RA (l : HLinked2) (Ii : SInst) (ri : CRound Ii.E Ii.F) (r : SRound sigU sigU sigU) : Prop :=
  ∃ y, RdI l.imp Ii ri y ∧
    HBR (implsH (l.host.length + l.exp.exports.length) (l.wireArgs ++ l.hostArgs)) y
      (downBy (l.host.length + l.exp.exports.length) r.up)

theorem rb_q {r : SRound sigU sigU sigU}
    {co : (Fin l.imp.exports.length × List IVal) × Option (List IVal) ×
      List (Round (sigN l.host.length))} (hB : RB l r co) :
    r.q = (l.host.length + l.exp.exports.length + co.1.1.val, .vals co.1.2) := by
  obtain ⟨u, hv, q, a, cs, cs', rfl, hd, -⟩ := hB
  have h₁ : ((co.1.1.val, .vals co.1.2) : Nat × Payload) = q := congrArg CRound.q hd
  subst h₁
  exact congrArg CRound.q hv

theorem hbr_q {y : CRound sigU sigU} {r : SRound sigU sigU sigU}
    (h : HBR (implsH (l.host.length + l.exp.exports.length) (l.wireArgs ++ l.hostArgs)) y
      (downBy (l.host.length + l.exp.exports.length) r.up)) :
    y.q = (r.q.1 - (l.host.length + l.exp.exports.length), r.q.2) := by
  obtain ⟨q, a, cs, cs', rfl, hd, -⟩ := h
  exact (congrArg CRound.q hd).symm

theorem subs_eq :
    ∀ {S : List (CRound sigU sigU)} {X : List (Round (sigN l.imp.imports.length))},
      (∀ s ∈ S, s.cs = csOf l.host.length (CRound.toRound s)) →
      S.map CRound.toRound = X.map (rn l) → (∀ x ∈ X, Cls l x) → S = X.map (sx l)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | s :: S, x :: X, hS, h, hX => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [subs_eq (fun s' hs' => hS s' (List.mem_cons_of_mem _ hs')) h₂
      (fun x' hx' => hX x' (List.mem_cons_of_mem _ hx')), List.map_cons]
    refine congrArg (· :: X.map (sx l)) ?_
    have hcs := hS s List.mem_cons_self
    obtain ⟨sq, scs, sa⟩ := s
    have h₁' : (⟨sq, sa⟩ : Round sigU) = ⟨(sx l x).q, (sx l x).a⟩ := h₁
    obtain ⟨rfl, h₃⟩ := Sigma.mk.inj h₁'
    cases eq_of_heq h₃
    have hcs' : scs = csOf l.host.length ⟨(sx l x).q, (sx l x).a⟩ := hcs
    subst hcs'
    have hx := hX x List.mem_cons_self
    have e : csOf l.host.length ⟨(sx l x).q, (sx l x).a⟩ = (sx l x).cs := by
      by_cases hw : x.1.1.val < l.wire.length
      · have h₄ : ¬ (l.host.length + l.wire.getD x.1.1.val 0 < l.host.length) := by omega
        rw [sx_wired hw]
        simp only [csOf, h₄, ↓reduceIte]
      · have h₄ : x.1.1.val - l.wire.length < l.host.length := by
          rcases hx with hx | hx
          · exact absurd hx.1 hw
          · exact hx.2
        rw [sx_host hw]
        simp only [csOf, h₄, ↓reduceIte]
    rw [e]

/-- **A round of the importer's instance read back through the layers of the linked
component**, its host calls those of the session play. -/
theorem round_ofH (hw : l.WireTy) {Ii : SInst} {ri : CRound Ii.E Ii.F}
    {r : SRound sigU sigU sigU}
    {co : (Fin l.imp.exports.length × List IVal) × Option (List IVal) ×
      List (Round (sigN l.host.length))}
    (hA : RA l Ii ri r) (hB : RB l r co)
    (hS : ∀ s ∈ r.subs, s.cs = csOf l.host.length (CRound.toRound s)) :
    ∃ d : Linked2.SessRound l.toL2 Ii, d.Ok ∧ SessRound.r d = ri ∧
      r.subs.map CRound.toRound = d.dss.flatten.map (rn l) ∧
      ((d.j, d.vs) = co.1 ∧ d.ans = co.2.1.map .vals ∧ l.hostCalls d.dss.flatten = co.2.2) ∧
      ∀ y ∈ d.dss.flatten, WTH l y := by
  obtain ⟨⟨j, vs⟩, o, hh⟩ := co
  obtain ⟨rq, subs, ra⟩ := r
  obtain ⟨u, hv, q₂, a₂, cs₂, cs₂', rfl, hd, H₂⟩ := hB
  have hd' : (⟨(j.val, .vals vs), hh, o.map .vals⟩ : CRound (sigN l.host.length) sigU) =
      ⟨q₂, cs₂', a₂⟩ := hd
  cases hd'
  have hv' : (⟨rq, subs.flatMap (·.cs), ra⟩ : CRound sigU sigU) =
      ⟨(l.host.length + l.exp.exports.length + j.val, .vals vs), cs₂, o.map .vals⟩ := hv
  cases hv'
  obtain ⟨y, hRd, q, a, cs, cs', rfl, hy, H⟩ := hA
  have hy' : (⟨(l.host.length + l.exp.exports.length + j.val - (l.host.length +
      l.exp.exports.length), .vals vs), subs.map CRound.toRound, o.map .vals⟩ :
      CRound sigU sigU) = ⟨q, cs', a⟩ := hy
  rw [Nat.add_sub_cancel_left] at hy'
  cases hy'
  obtain ⟨rf, rcs, rw'⟩ := ri
  obtain ⟨j', vs', xs, dss, hxq, hcl, h₁, h₂, hF, hxcs, hxa⟩ := hRd
  have hxq' : ((j.val, Payload.vals vs) : Nat × Payload) = (j'.val, .vals vs') := hxq
  simp only [Prod.mk.injEq, Payload.vals.injEq] at hxq'
  obtain ⟨hj, rfl⟩ := hxq'
  have hj' : j = j' := Fin.ext hj
  subst hj'
  have hxcs' : cs = dss.flatten.map Round.forget := hxcs
  subst hxcs'
  have hwt : ∀ x ∈ dss.flatten, WTH l x := by
    intro x hx
    obtain ⟨ds, hds, hx⟩ := List.mem_flatten.mp hx
    obtain ⟨x', hx'⟩ := forall₂_mem_right hF ds hds
    obtain ⟨nm, ft, ws, hft, hp, hck⟩ := impRel_typed hx' x hx
    exact wth_of hw hft hp hck
  have hcls : ∀ x ∈ dss.flatten, Cls l x := fun x hx => cls_of_wth (hwt x hx)
  have hsub := hrounds_impl_inv hcls H
  have hsubs : subs = dss.flatten.map (sx l) := subs_eq hS hsub hcls
  refine ⟨⟨j, vs, rf, rcs, rw', dss⟩, ⟨xs, hcl, h₁, h₂, hF⟩, rfl, hsub, ⟨rfl, hxa.symm, ?_⟩,
    hwt⟩
  rw [hsubs, flatMap_sx_cs, hCalls_eq hcls] at H₂
  exact (hrounds_widenH_inv H₂).symm

theorem build_roundsH (hw : l.WireTy) {Ii : SInst} :
    ∀ {ri : List (CRound Ii.E Ii.F)} {L : List (SRound sigU sigU sigU)}
      {cos : List ((Fin l.imp.exports.length × List IVal) × Option (List IVal) ×
        List (Round (sigN l.host.length)))},
      List.Forall₂ (RA l Ii) ri L → List.Forall₂ (RB l) L cos →
      (∀ r ∈ L, ∀ s ∈ r.subs, s.cs = csOf l.host.length (CRound.toRound s)) →
      ∃ ds : List (Linked2.SessRound l.toL2 Ii), (∀ d ∈ ds, d.Ok) ∧
        ds.map SessRound.r = ri ∧
        (L.flatMap (·.subs)).map CRound.toRound =
          (ds.flatMap fun d => d.dss.flatten).map (rn l) ∧
        List.Forall₂ (fun d co => (d.j, d.vs) = co.1 ∧ d.ans = co.2.1.map .vals ∧
          l.hostCalls d.dss.flatten = co.2.2) ds cos ∧
        ∀ y ∈ ds.flatMap (fun d => d.dss.flatten), WTH l y
  | _, _, _, .nil, .nil, _ =>
    ⟨[], fun _ h => (nomatch h), rfl, rfl, .nil, fun _ h => (nomatch h)⟩
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂, hS => by
    obtain ⟨d, hOk, hr, hcs, hjo, hwt⟩ := round_ofH hw h₁ h₂ (hS _ List.mem_cons_self)
    obtain ⟨ds, hOks, hrs, hcss, hF, hwts⟩ :=
      build_roundsH hw t₁ t₂ fun r hr => hS r (List.mem_cons_of_mem _ hr)
    refine ⟨d :: ds, ?_, by rw [List.map_cons, hr, hrs], ?_, .cons hjo hF, ?_⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact hOk
      · exact hOks d' hd'
    · rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, hcs, hcss]
    · intro y hy
      rw [List.flatMap_cons, List.mem_append] at hy
      rcases hy with hy | hy
      · exact hwt y hy
      · exact hwts y hy

/-! ## The session -/

/-- **Rounds of the importer and an `ExpRunH` are a specification session.** -/
theorem sessSpecH_of {Ie Ii : SInst} :
    ∀ (ds : List (Linked2.SessRound l.toL2 Ii))
      (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
      (hs : List (List (Round (sigN l.host.length)))) {u π π' : Store Nat} {q : Ii.HState},
      List.Forall₂ (fun d co => (d.j, d.vs) = co.1 ∧ d.ans = co.2.1.map .vals ∧
        l.hostCalls d.dss.flatten = co.2.2) ds (calls.zip (outs.zip hs)) →
      calls.length = outs.length → calls.length = hs.length → (∀ d ∈ ds, d.Ok) →
      Ii.Path P (.idle u) (ds.flatMap Linked2.SessRound.instMoves) q →
      HLinked2.ExpRunH P l Ie π (ds.flatMap fun d => d.dss.flatten) π' →
      ∃ u', HLinked2.SessSpec P l Ie Ii u π calls outs hs u' π'
  | [], calls, outs, hs, u, π, π', q, hF, hlen, hlen', _, _, hrun => by
    cases hrun
    have hz : calls.zip (outs.zip hs) = [] := List.forall₂_nil_left_iff.mp hF
    have hc : calls = [] := by
      rcases List.zip_eq_nil_iff.mp hz with h | h
      · exact h
      · rcases List.zip_eq_nil_iff.mp h with h | h
        · subst h
          exact List.length_eq_zero_iff.mp hlen
        · subst h
          exact List.length_eq_zero_iff.mp hlen'
    subst hc
    have ho : outs = [] := List.length_eq_zero_iff.mp hlen.symm
    have hh : hs = [] := List.length_eq_zero_iff.mp hlen'.symm
    subst ho hh
    exact ⟨u, .nil u π⟩
  | d :: ds, calls, outs, hs, u, π, π', q, hF, hlen, hlen', hOk, hp, hrun => by
    rcases calls with _ | ⟨c, cs⟩
    · cases hF
    rcases outs with _ | ⟨o, os⟩
    · cases hF
    rcases hs with _ | ⟨h, hs⟩
    · cases hF
    have hF' : List.Forall₂ (fun (d : Linked2.SessRound l.toL2 Ii)
        (co : (Fin l.imp.exports.length × List IVal) × Option (List IVal) ×
          List (Round (sigN l.host.length))) =>
        (d.j, d.vs) = co.1 ∧ d.ans = co.2.1.map .vals ∧ l.hostCalls d.dss.flatten = co.2.2)
        (d :: ds) ((c, (o, h)) :: cs.zip (os.zip hs)) := hF
    obtain ⟨⟨hdc, hans, hhc⟩, hF''⟩ := List.forall₂_cons.mp hF'
    rw [List.flatMap_cons] at hp hrun
    obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hp
    obtain ⟨u₁, rfl⟩ := path_ans_idle hp₁
    obtain ⟨π₁, hr₁, hr₂⟩ := expRunH_split _ _ hrun
    obtain ⟨u', hS⟩ := sessSpecH_of ds cs os hs hF'' (by simpa using hlen) (by simpa using hlen')
      (fun d' hd' => hOk d' (List.mem_cons_of_mem _ hd')) hp₂ hr₂
    subst hdc hhc
    exact ⟨u', .round d (hOk d List.mem_cons_self) hp₁ hr₁ hans hS⟩

/-! ## The theorem -/

/-- **The IR to specification direction of linked sessions with host imports**: a typed session
play of `l.toComp.den (impSem P)`, its host calls visible, is the play of an `HLinked2.SessSpec`
session from the instances' stores with the same host calls. -/
theorem hlinked2_irToSpec (P : Profile) (l : HLinked2) (hl : l.Adequate) {Ie Ii : SInst}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (hs : List (List (Round (sigN l.host.length)))) (ht : SimpleI.TypedCalls l.imp calls)
    (hlen : calls.length = outs.length) (hlen' : calls.length = hs.length)
    (h : l.sessMoves calls outs hs ∈ l.toComp.den (impSem P)) :
    ∃ u' π' : Store Nat, HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π' := by
  rw [sessMovesH_eq] at h
  have h₀ : cplay ((calls.zip (outs.zip hs)).map (topRH l)) ∈
      ((Strategy.ofHandler (widenH l.host.length)).comp (l.toComp.denU (impSem P))).comp
        (Strategy.ofHandler (narrowH l.toComp.exports.length)) := h
  -- `atSizes`
  obtain ⟨low₁, H₁, h₁⟩ := hc_inv (oneShot_narrowH _) h₀
  rw [hc_narrowH_inv H₁] at h₁
  obtain ⟨up₂, H₂, h₂⟩ := hb_inv (oneShot_widenH _) h₁
  have F₂ : List.Forall₂ (fun u co => HBR (widenH l.host.length) u (narrowC (topRH l co))) up₂
      (calls.zip (outs.zip hs)) :=
    forall₂_map_right (f := topRH l) (forall₂_map_right (f := narrowC) (hb_forall₂ H₂))
  have hlt₂ : ∀ r ∈ up₂, r.q.1 < l.imp.exports.length := by
    intro r hr
    obtain ⟨co, q, a, cs, cs', rfl, hd, -⟩ := forall₂_mem_left F₂ r hr
    have e : ((co.1.1.val, .vals co.1.2) : Nat × Payload) = q := congrArg CRound.q hd
    rw [← e]
    exact co.1.1.isLt
  -- the export handler
  rw [denU_toCompH] at h₂
  obtain ⟨low₃, H₃, h₃⟩ := hc_inv (oneShot_implsH _ _) h₂
  rw [hc_exportsH_inv l H₃ hlt₂] at h₃
  -- the second environment over the first
  have h₃' : cplay (up₂.map (shiftC (l.host.length + l.exp.exports.length))) ∈
      (env1 (impSem P) l).comp (((Strategy.id sigU).pair (impNodeH (impSem P) l)).comp
        (Strategy.ofHandler (splitH (l.host.length + l.exp.exports.length)))) := h₃
  obtain ⟨L, hτ, hσ, hvis⟩ := serveC_inv h₃'
  have B : List.Forall₂ (RB l) L (calls.zip (outs.zip hs)) :=
    forall₂_comp (forall₂_of_map_eq hvis) F₂
  -- `splitH`, the pairing and the importer's node
  obtain ⟨low₆, H₆, h₆⟩ := hc_inv (oneShot_splitH _) hτ
  have hge : ∀ r ∈ L.map SRound.up, l.host.length + l.exp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨co, hco⟩ := forall₂_mem_left B r' hr'
    show _ ≤ r'.q.1
    rw [rb_q hco]
    exact Nat.le_add_right _ _
  rw [hc_splitH_inv H₆ hge] at h₆
  have hN := cplay_of_pair_inr h₆
  obtain ⟨up₇, H₇, h₇⟩ := hb_inv (oneShot_implsH _ _) hN
  have F₇ : List.Forall₂ (fun y r => HBR (implsH (l.host.length + l.exp.exports.length)
      (l.wireArgs ++ l.hostArgs)) y (downBy (l.host.length + l.exp.exports.length) r.up))
      up₇ L :=
    forall₂_map_right (f := SRound.up)
      (forall₂_map_right (f := downBy (l.host.length + l.exp.exports.length)) (hb_forall₂ H₇))
  -- the importer
  have htop : ∀ y ∈ up₇, TopI l.imp y := by
    intro y hy
    obtain ⟨co, ⟨r, hyr, hrc⟩, hco⟩ := forall₂_mem_left
      (forall₂_and_right (forall₂_comp F₇ B) fun co hco => (List.of_mem_zip hco).1) y hy
    refine ⟨co.1.1, co.1.2, ?_, ht _ hco⟩
    rw [hbr_q hyr, rb_q hrc]
    show ((l.host.length + l.exp.exports.length + co.1.1.val -
      (l.host.length + l.exp.exports.length), Payload.vals co.1.2) : Nat × Payload) = _
    rw [Nat.add_sub_cancel_left]
  obtain ⟨ri, hri, F₈⟩ := imp_readback hl.impGood hIi htop h₇
  have A : List.Forall₂ (RA l Ii) ri L := forall₂_comp F₈ F₇
  -- the first environment
  obtain ⟨hS, hE⟩ := env1_inv hσ
  obtain ⟨ds, hOk, hr, hX, hF, hWT⟩ := build_roundsH hl.wireTy A B fun r hr s hs =>
    hS s (List.mem_flatMap.mpr ⟨r, hr, hs⟩)
  have hcls : ∀ x ∈ ds.flatMap (fun d => d.dss.flatten), Cls l x := fun x hx =>
    cls_of_wth (hWT x hx)
  rw [hX, filterMap_rn _ hcls] at hE
  -- the exporter
  have hspec := expNodeH_specRoundsT hl.expGood hIe hE
  obtain ⟨s', hS'⟩ := sessRounds_of_specRoundsT hspec (aCall_lt hcls)
  have hrun := expRunH_of_sessRounds _ hWT hS'
  -- the session
  obtain ⟨q, hq⟩ := Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mp hri
  rw [← hr, cplay_r] at hq
  obtain ⟨u', hSp⟩ := sessSpecH_of ds calls outs hs hF hlen hlen' hOk hq hrun
  exact ⟨u', s', hSp⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
