module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Linked
public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.Main
public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Defs

/-!
# Ill-typed calls of a linked component

The plays of `l.toComp.den (impSem P)` may contain ill-typed export questions (`Linked2.typedQ`
fails). The linked export handler forwards every question to the importer's node; there the
importer's own export handler answers an ill-typed question by a trap at once, with no lower
calls (`xb_bad`), and passes a typed one to its core instance (`xb_good`). So the ill-typed rounds
can be removed from a play, and inserted into one, without touching the rest:

* `den_top`, `den_of_top`: the complete rounds of the linked denotation are the rounds `cl` of
  the importer's node whose lower calls, all together and in order, are complete rounds of the
  exporter's environment;
* `impNode_inv`, `impNode_of`: in the importer's node, the ill-typed rounds are exactly
  trap-answered rounds without lower calls, and removing or inserting them keeps a play;
* `den_inv`, `den_of`: the same for the linked denotation.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Lists -/

section Lists

variable {α β : Type}

theorem forall₂_filter {R : α → β → Prop} {p : α → Bool} {p' : β → Bool}
    (hR : ∀ a b, R a b → p a = p' b) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs →
      List.Forall₂ R (as.filter p) (bs.filter p')
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons h t => by
    have e := hR a b h
    cases hb : p' b with
    | false =>
      rw [List.filter_cons_of_neg (by simp [e, hb]), List.filter_cons_of_neg (by simp [hb])]
      exact forall₂_filter hR t
    | true =>
      rw [List.filter_cons_of_pos (by simp [e, hb]), List.filter_cons_of_pos hb]
      exact .cons h (forall₂_filter hR t)

/-- Re-inserting the rounds a filter removed, along a relation preserving the filter. -/
theorem forall₂_unfilter {R : α → β → Prop} {p : α → Bool} {p' : β → Bool} (f : β → α)
    (hR : ∀ a b, R a b → p a = p' b) :
    ∀ (bs : List β) (as' : List α), (∀ b ∈ bs, p' b = false → R (f b) b) →
      List.Forall₂ R as' (bs.filter p') →
      ∃ as, List.Forall₂ R as bs ∧ as.filter p = as' ∧
        ∀ a ∈ as, p a = false → ∃ b ∈ bs, a = f b
  | [], as', _, h => by
    rw [List.filter_nil] at h
    cases h
    exact ⟨[], .nil, rfl, fun _ h => nomatch h⟩
  | b :: bs, as', hf, h => by
    have hf' : ∀ b' ∈ bs, p' b' = false → R (f b') b' :=
      fun b' hb' => hf b' (List.mem_cons_of_mem _ hb')
    cases hb : p' b with
    | false =>
      rw [List.filter_cons_of_neg (by simp [hb])] at h
      obtain ⟨as, H, e, hm⟩ := forall₂_unfilter f hR bs as' hf' h
      have hfb := hf b List.mem_cons_self hb
      refine ⟨f b :: as, .cons hfb H, ?_, ?_⟩
      · rw [List.filter_cons_of_neg (by simp [hR _ _ hfb, hb]), e]
      · intro a ha hpa
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨b, List.mem_cons_self, rfl⟩
        · obtain ⟨b', hb', rfl⟩ := hm a ha hpa
          exact ⟨b', List.mem_cons_of_mem _ hb', rfl⟩
    | true =>
      rw [List.filter_cons_of_pos hb] at h
      obtain ⟨a, as'', hab, H'', rfl⟩ : ∃ a as'', R a b ∧ List.Forall₂ R as'' (bs.filter p') ∧
          as' = a :: as'' := by
        cases h with
        | cons hab H'' => exact ⟨_, _, hab, H'', rfl⟩
      obtain ⟨as, H, e, hm⟩ := forall₂_unfilter f hR bs as'' hf' H''
      refine ⟨a :: as, .cons hab H, ?_, ?_⟩
      · rw [List.filter_cons_of_pos (by rw [hR _ _ hab, hb]), e]
      · intro a' ha' hpa
        rcases List.mem_cons.mp ha' with rfl | ha'
        · rw [hR _ _ hab, hb] at hpa
          cases hpa
        · obtain ⟨b', hb', rfl⟩ := hm a' ha' hpa
          exact ⟨b', List.mem_cons_of_mem _ hb', rfl⟩

theorem forall₂_mem_right' {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ b ∈ bs, ∃ a ∈ as, R a b
  | _, _, .nil, _, hb => nomatch hb
  | _, _, .cons h t, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_mem_right' t b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem forall₂_map_eq {f : α → β} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ (fun a b => f a = b) as bs → as.map f = bs
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [List.map_cons, h, forall₂_map_eq t]

end Lists

/-! ## Handlers -/

section Handlers

variable {E : Sig.{0}} {h : Handler sigU sigU}

/-- A round answered at once has no lower calls and the handler's answer. -/
theorem hc_pure_mem : ∀ {up : List (CRound E sigU)} {low : List (CRound E sigU)}, HC h up low →
    ∀ r ∈ up, ∀ a, h r.q = .pure a → r.cs = [] ∧ r.a = a
  | _, _, .nil, _, hr, _, _ => nomatch hr
  | _, _, .pure (q := q) (a := a₀) hq H, r, hr, a, ha => by
    rcases List.mem_cons.mp hr with rfl | hr
    · have ha' : h q = .pure a := ha
      rw [hq] at ha'
      exact ⟨rfl, Prog.pure.inj ha'⟩
    · exact hc_pure_mem H r hr a ha
  | _, _, .call (q := q) hq _ H, r, hr, a, ha => by
    rcases List.mem_cons.mp hr with rfl | hr
    · have ha' : h q = .pure a := ha
      rw [hq] at ha'
      cases ha'
    · exact hc_pure_mem H r hr a ha

/-- A round answered by one call has the continuation's answer to some lower answer. -/
theorem hc_call_mem : ∀ {up : List (CRound E sigU)} {low : List (CRound E sigU)}, HC h up low →
    ∀ r ∈ up, ∀ q' k, h r.q = .call q' k → ∃ a', k a' = .pure r.a
  | _, _, .nil, _, hr, _, _, _ => nomatch hr
  | _, _, .pure (q := q) hq H, r, hr, q', k, hk => by
    rcases List.mem_cons.mp hr with rfl | hr
    · have hk' : h q = .call q' k := hk
      rw [hq] at hk'
      cases hk'
    · exact hc_call_mem H r hr q' k hk
  | _, _, .call (q := q) (a' := a') hq hk₀ H, r, hr, q', k, hk => by
    rcases List.mem_cons.mp hr with rfl | hr
    · have hk' : h q = .call q' k := hk
      rw [hq] at hk'
      cases hk'
      exact ⟨a', hk₀⟩
    · exact hc_call_mem H r hr q' k hk

/-- Removing the rounds answered at once. -/
theorem hc_filter (p : Nat × Payload → Bool) :
    ∀ {up : List (CRound E sigU)} {low : List (CRound E sigU)}, HC h up low →
      (∀ r ∈ up, p r.q = true → ∀ a, h r.q ≠ .pure a) →
      (∀ r ∈ up, p r.q = false → ∃ a, h r.q = .pure a) →
      HC h (up.filter fun r => p r.q) low
  | _, _, .nil, _, _ => .nil
  | _, _, .pure (q := q) (a := a) hq H, hp, hn => by
    have hpq : p q = false := by
      cases e : p q with
      | false => rfl
      | true => exact absurd hq (hp _ List.mem_cons_self e a)
    rw [List.filter_cons_of_neg (by simp [hpq])]
    exact hc_filter p H (fun r hr => hp r (List.mem_cons_of_mem _ hr))
      (fun r hr => hn r (List.mem_cons_of_mem _ hr))
  | _, _, .call (q := q) hq hk H, hp, hn => by
    have hpq : p q = true := by
      cases e : p q with
      | true => rfl
      | false =>
        obtain ⟨a, ha⟩ := hn _ List.mem_cons_self e
        have ha' : h q = .pure a := ha
        rw [hq] at ha'
        cases ha'
    rw [List.filter_cons_of_pos (by simp [hpq])]
    exact .call hq hk (hc_filter p H (fun r hr => hp r (List.mem_cons_of_mem _ hr))
      (fun r hr => hn r (List.mem_cons_of_mem _ hr)))

/-- Inserting rounds answered at once. -/
theorem hc_unfilter (p : Nat × Payload → Bool) :
    ∀ (up : List (CRound E sigU)) {low : List (CRound E sigU)},
      HC h (up.filter fun r => p r.q) low →
      (∀ r ∈ up, p r.q = false → r.cs = [] ∧ h r.q = .pure r.a) → HC h up low
  | [], _, H, _ => by
    rw [List.filter_nil] at H
    exact H
  | ⟨q, cs, a⟩ :: up, low, H, hp => by
    have hp' : ∀ r ∈ up, p r.q = false → r.cs = [] ∧ h r.q = .pure r.a :=
      fun r hr => hp r (List.mem_cons_of_mem _ hr)
    cases e : p q with
    | false =>
      rw [List.filter_cons_of_neg (by simp [e])] at H
      obtain ⟨hcs, hq⟩ := hp _ List.mem_cons_self e
      have hcs' : cs = [] := hcs
      subst hcs'
      exact .pure hq (hc_unfilter p up H hp')
    | true =>
      rw [List.filter_cons_of_pos (by simp [e])] at H
      cases H with
      | pure hq H' => exact .pure hq (hc_unfilter p up H' hp')
      | call hq hk H' => exact .call hq hk (hc_unfilter p up H' hp')

end Handlers

section Below

variable {E F G : Sig.{0}}

theorem hb_of_forall₂ {h : Handler E F} :
    ∀ {up : List (CRound F G)} {low : List (CRound E G)}, List.Forall₂ (HBR h) up low → HB h up low
  | _, _, .nil => .nil
  | _, _, .cons hr t => by
    obtain ⟨_, _, _, _, rfl, rfl, Hc⟩ := hr
    exact .cons Hc (hb_of_forall₂ t)

theorem hbr_q {h : Handler E F} {u : CRound F G} {d : CRound E G} (hr : HBR h u d) : u.q = d.q := by
  obtain ⟨_, _, _, _, rfl, rfl, _⟩ := hr
  rfl

end Below

/-! ## The importer's export handler -/

section Export

variable (l : Linked2)

/-- The importer's export handler. -/
abbrev XB : Handler sigU sigU :=
  exportsH (l.imp.imports.length + l.imp.mod.exports.length) l.imp.toComp.exports

/-- Whether a question is a typed call. -/
def good (q : Nat × Payload) : Bool := (l.typedQ q).isSome

variable {l}

theorem typedQ_some {q : Nat × Payload} {j : Fin l.imp.exports.length} {vs : List IVal}
    (h : l.typedQ q = some (j, vs)) :
    q = (j.val, .vals vs) ∧ ValTy.checkList l.imp.exports[j].ty.params vs = true := by
  obtain ⟨j', p⟩ := q
  cases p with
  | flat _ => cases h
  | vals vs' =>
    by_cases hj : j' < l.imp.exports.length
    · cases hc : ValTy.checkList l.imp.exports[j'].ty.params vs' with
      | false => simp [Linked2.typedQ, hj, hc] at h
      | true =>
        simp only [Linked2.typedQ, hj, hc, ↓reduceDIte, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hc⟩
    · simp [Linked2.typedQ, hj] at h

theorem typedQ_typed {j : Fin l.imp.exports.length} {vs : List IVal}
    (h : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    l.typedQ (j.val, .vals vs) = some (j, vs) := by
  have h' : ValTy.checkList l.imp.exports[j.val].ty.params vs = true := h
  simp [Linked2.typedQ, j.isLt, h']

theorem xb_flat (j : Nat) (xs : List Flat) : XB l (j, .flat xs) = .pure none := by
  simp only [XB, exportsH, implsH, SimpleI.toComp, Comp.exports_mk, List.getElem?_map]
  cases l.imp.exports[j]? <;> rfl

/-- **An ill-typed question is answered by a trap at once.** -/
theorem xb_bad (hc : l.imp.Good) {q : Nat × Payload} (h : l.typedQ q = none) :
    XB l q = .pure none := by
  obtain ⟨j, p⟩ := q
  cases p with
  | flat xs => exact xb_flat j xs
  | vals vs =>
    by_cases hj : j < l.imp.exports.length
    · have hck : ValTy.checkList l.imp.exports[j].ty.params vs = false := by
        cases e : ValTy.checkList l.imp.exports[j].ty.params vs with
        | false => rfl
        | true => simp [Linked2.typedQ, hj, e] at h
      rw [XB, exportsH_toCompI l.imp hj vs (core_lt hc ⟨j, hj⟩),
        SessionAdequacy.checkLower_none_of hck]
    · simp only [XB, exportsH, implsH, SimpleI.toComp, Comp.exports_mk, List.getElem?_map,
        List.getElem?_eq_none (Nat.le_of_not_lt hj)]
      rfl

/-- **A typed question is passed to the core instance**, its answer lifted. -/
theorem xb_good (hc : l.imp.Good) {q : Nat × Payload} {j : Fin l.imp.exports.length}
    {vs : List IVal} (h : l.typedQ q = some (j, vs)) :
    XB l q = .call (l.imp.exports[j].core + l.imp.imports.length,
        .flat (lowerArgs l.imp.exports[j].ty.params vs))
      fun n => .pure (n.bind (Adapter.up (.lift l.imp.exports[j].ty))) := by
  obtain ⟨rfl, hck⟩ := typedQ_some h
  exact exportsH_typed hc hck

theorem up_lift_form (ft : FuncTy) :
    ∀ a : Option Payload, a.bind (Adapter.up (.lift ft)) = none ∨
      ∃ ws, a.bind (Adapter.up (.lift ft)) = some (.vals ws)
  | none => .inl rfl
  | some (.vals _) => .inl rfl
  | some (.flat ys) => by
    cases h : liftArgs ft.results ys with
    | none => exact .inl (by simp [Adapter.up, h])
    | some ws => exact .inr ⟨ws, by simp [Adapter.up, h]⟩

theorem good_false {q : Nat × Payload} (h : good l q = false) : l.typedQ q = none := by
  unfold good at h
  cases e : l.typedQ q with
  | none => rfl
  | some _ => rw [e] at h; cases h

theorem good_true {q : Nat × Payload} (h : good l q = true) :
    ∃ jv, l.typedQ q = some jv := by
  unfold good at h
  cases e : l.typedQ q with
  | none => rw [e] at h; cases h
  | some jv => exact ⟨jv, rfl⟩

end Export

/-! ## The importer's node -/

section Node

variable {P : Profile} {l : Linked2}

/-- **Rounds of the importer's node**: the ill-typed rounds are trap-answered rounds without
lower calls, the typed ones are answered by a trap or values, and the typed rounds alone are a
play. -/
theorem impNode_inv (hc : l.imp.Good) {cl : List (CRound sigU sigU)}
    (h : cplay cl ∈ impNode (impSem P) l) :
    (∀ r ∈ cl, good l r.q = false → r.cs = [] ∧ r.a = none) ∧
    (∀ r ∈ cl, good l r.q = true → r.a = none ∨ ∃ ws, r.a = some (.vals ws)) ∧
    cplay (cl.filter fun r => good l r.q) ∈ impNode (impSem P) l := by
  obtain ⟨up, HBu, hup⟩ := hb_inv (oneShot_implsH _ _) h
  have F := hb_forall₂ HBu
  rw [denU_toCompI] at hup
  obtain ⟨low, HC₁, hlow⟩ := hc_inv (oneShot_implsH _ _) hup
  have hbad : ∀ u ∈ up, good l u.q = false → u.cs = [] ∧ u.a = none := fun u hu hb =>
    hc_pure_mem HC₁ u hu none (xb_bad hc (good_false hb))
  have hgood : ∀ u ∈ up, good l u.q = true → u.a = none ∨ ∃ ws, u.a = some (.vals ws) := by
    intro u hu hg
    obtain ⟨⟨j, vs⟩, e⟩ := good_true hg
    obtain ⟨a', ha'⟩ := hc_call_mem HC₁ u hu _ _ (xb_good hc e)
    rw [← Prog.pure.inj ha']
    exact up_lift_form _ a'
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hb
    obtain ⟨u, hu, hur⟩ := forall₂_mem_right' F r hr
    have hq := hbr_q hur
    obtain ⟨hcs, ha⟩ := hbad u hu (by rw [hq]; exact hb)
    obtain ⟨q, a, cs, cs', rfl, rfl, Hc⟩ := hur
    have hcs' : cs = [] := hcs
    subst hcs'
    cases Hc
    exact ⟨rfl, ha⟩
  · intro r hr hg
    obtain ⟨u, hu, hur⟩ := forall₂_mem_right' F r hr
    have hq := hbr_q hur
    have hu' := hgood u hu (by rw [hq]; exact hg)
    obtain ⟨q, a, cs, cs', rfl, rfl, -⟩ := hur
    exact hu'
  · have HC₂ := hc_filter (good l) HC₁
      (fun r _ hg a e => by
        obtain ⟨⟨j, vs⟩, e'⟩ := good_true hg
        have e₂ := (xb_good hc e').symm.trans e
        cases e₂)
      (fun r _ hb => ⟨none, xb_bad hc (good_false hb)⟩)
    have hU : cplay (up.filter fun r => good l r.q) ∈ l.imp.toComp.denU (impSem P) := by
      rw [denU_toCompI]
      exact cplay_comp_ofHandler HC₂ hlow
    exact cplay_ofHandler_comp
      (hb_of_forall₂ (forall₂_filter (fun _ _ hr => congrArg (good l) (hbr_q hr)) F)) hU

/-- **Inserting ill-typed rounds into a play of the importer's node**: trap-answered rounds
without lower calls. -/
theorem impNode_of (hc : l.imp.Good) {cl : List (CRound sigU sigU)}
    (hbad : ∀ r ∈ cl, good l r.q = false → r.cs = [] ∧ r.a = none)
    (h : cplay (cl.filter fun r => good l r.q) ∈ impNode (impSem P) l) :
    cplay cl ∈ impNode (impSem P) l := by
  obtain ⟨up', HBu, hup'⟩ := hb_inv (oneShot_implsH _ _) h
  obtain ⟨up, F, e, hm⟩ := forall₂_unfilter (R := HBR (implsH l.exp.exports.length (wireArgs l)))
    (p := fun u => good l u.q) (p' := fun r => good l r.q) (fun r => r)
    (fun _ _ hr => congrArg (good l) (hbr_q hr)) cl up'
    (by
      intro r hr hb
      obtain ⟨hcs, -⟩ := hbad r hr hb
      obtain ⟨q, cs, a⟩ := r
      have hcs' : cs = [] := hcs
      subst hcs'
      exact ⟨q, a, [], [], rfl, rfl, .nil⟩)
    (hb_forall₂ HBu)
  rw [denU_toCompI] at hup'
  obtain ⟨low, HC₁, hlow⟩ := hc_inv (oneShot_implsH _ _) hup'
  rw [← e] at HC₁
  have HC₂ := hc_unfilter (good l) up HC₁ (by
    intro u hu hb
    obtain ⟨r, hr, e'⟩ := hm u hu hb
    have e'' : u = r := e'
    rw [e''] at hb ⊢
    obtain ⟨hcs, ha⟩ := hbad r hr hb
    refine ⟨hcs, ?_⟩
    rw [ha]
    exact xb_bad hc (good_false hb))
  have hU : cplay up ∈ l.imp.toComp.denU (impSem P) := by
    rw [denU_toCompI]
    exact cplay_comp_ofHandler HC₂ hlow
  exact cplay_ofHandler_comp (hb_of_forall₂ F) hU

end Node

/-! ## The top layers -/

section Top

variable {P : Profile} {l : Linked2}

/-- A round of the linked component as a question of its environment. -/
def shiftR (l : Linked2) (x : Round (sigN l.toComp.exports.length)) : Round sigU :=
  ⟨(l.exp.exports.length + x.1.1.val, x.1.2), x.2⟩

/-- The linked export handler forwards every export round to the importer's side. -/
theorem hrounds_exportsL_inv' (l : Linked2) :
    ∀ (L : List (Round (sigN l.toComp.exports.length))) (low : List (Round sigU)),
      HRounds (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)
        (L.map Round.forget) low → low = L.map (shiftR l)
  | [], _, H => by cases H; rfl
  | ⟨(j, p), a⟩ :: L, low, H => by
    have hj : j.val < l.imp.exports.length := by
      rw [← Linked2.exports_length_toComp]
      exact j.isLt
    have H' : HRounds (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)
        (⟨(j.val, p), a⟩ :: L.map Round.forget) low := H
    rcases hrounds_cons_inv H' with ⟨hq, -⟩ | ⟨q', k, a', low', rfl, hq, hk, H''⟩
    · rw [exportsH_toCompL l hj] at hq
      cases hq
    · rw [exportsH_toCompL l hj] at hq
      cases hq
      cases hk
      rw [hrounds_exportsL_inv' l L low' H'']
      rfl

theorem hrounds_shift (l : Linked2) : ∀ L : List (Round (sigN l.toComp.exports.length)),
    HRounds (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)
      (L.map Round.forget) (L.map (shiftR l))
  | [] => .nil
  | ⟨(j, p), a⟩ :: L => by
    have hj : j.val < l.imp.exports.length := by
      rw [← Linked2.exports_length_toComp]
      exact j.isLt
    show HRounds _ (⟨(j.val, p), a⟩ :: L.map Round.forget)
      (⟨(l.exp.exports.length + j.val, p), a⟩ :: L.map (shiftR l))
    exact .call (q := (j.val, p)) (q' := (l.exp.exports.length + j.val, p))
      (k := fun n => .pure n) (exportsH_toCompL l hj p) rfl (hrounds_shift l L)

theorem cplay_hide {E F G : Sig.{0}} : ∀ cl : List (CRound F G),
    cplay (cl.map (CRound.hide (E := E))) = twos (cl.map CRound.toRound)
  | [] => rfl
  | r :: cl => by
    show _ :: _ :: cplay (cl.map (CRound.hide (E := E))) = _ :: _ :: twos _
    rw [cplay_hide cl]
    rfl

/-- **The top layers read back**: complete rounds of the linked denotation are rounds of the
importer's node whose lower calls, all together and in order, are complete rounds of the
exporter's environment. -/
theorem den_top {L : List (Round (sigN l.toComp.exports.length))}
    (h : twos L ∈ l.toComp.den (impSem P)) :
    ∃ cl : List (CRound sigU sigU), cplay cl ∈ impNode (impSem P) l ∧
      twos (cl.flatMap (·.cs)) ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l) ∧
      cl.map CRound.toRound = L.map Round.forget := by
  unfold Comp.den atSizes at h
  obtain ⟨l₁, Hn, hl⟩ := hrounds_of_comp (oneShot_narrowH _) (fun s _ => noInl_sigN_nil rfl s) h
  rw [hrounds_narrowH_inv _ Hn] at hl
  have hEnv : ∀ t ∈ envL (impSem P) l, NoInl t :=
    noInl_comp (noInl_comp (noInl_ofHandler_pure pure_maskH0))
  have hU : ∀ t ∈ l.toComp.denU (impSem P), NoInl t := by
    rw [denU_toCompL]
    exact noInl_comp hEnv
  have hl₁ := twos_of_comp_noInl hU hl
  rw [denU_toCompL] at hl₁
  obtain ⟨l₂, H₂, hl₂⟩ := hrounds_of_comp (oneShot_implsH _ _) hEnv hl₁
  rw [hrounds_exportsL_inv' l L l₂ H₂] at hl₂
  have hσ : ∀ s ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l), NoInl s :=
    noInl_comp (noInl_ofHandler_pure pure_maskH0)
  obtain ⟨cl, hcl, hA, hmap⟩ := serve_inv hσ hl₂
  obtain ⟨low₁, H₁, hlow₁⟩ := hc_inv (oneShot_splitH _) hcl
  have hge : ∀ r ∈ cl, l.exp.exports.length ≤ r.q.1 := by
    intro r hr
    have hm : CRound.toRound r ∈ L.map (shiftR l) := hmap ▸ List.mem_map_of_mem hr
    obtain ⟨x, -, hx⟩ := List.mem_map.mp hm
    have hq : r.q = (shiftR l x).1 := (congrArg Sigma.fst hx).symm
    rw [hq]
    exact Nat.le_add_right _ _
  rw [hc_splitH_inv H₁ hge] at hlow₁
  have hN := cplay_of_pair_inr hlow₁
  refine ⟨cl.map (downBy l.exp.exports.length), hN, ?_, ?_⟩
  · rw [List.flatMap_map]
    exact hA
  · have e : ∀ (cl : List (CRound sigU sigU)) (L : List (Round (sigN l.toComp.exports.length))),
        cl.map CRound.toRound = L.map (shiftR l) →
        (cl.map (downBy l.exp.exports.length)).map CRound.toRound = L.map Round.forget := by
      intro cl
      induction cl with
      | nil =>
        intro L h
        cases L with
        | nil => rfl
        | cons _ _ => cases h
      | cons r cl ih =>
        intro L h
        cases L with
        | nil => cases h
        | cons x L =>
          simp only [List.map_cons, List.cons.injEq] at h ⊢
          refine ⟨?_, ih L h.2⟩
          obtain ⟨⟨q₁, q₂⟩, cs, a⟩ := r
          obtain ⟨⟨j, p⟩, b⟩ := x
          simp only [CRound.toRound, shiftR, Sigma.mk.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, -⟩ := h
          cases ha
          simp [CRound.toRound, downBy, Round.forget]
    exact e cl L hmap

/-- **The top layers built**: the converse of `den_top`. -/
theorem den_of_top {L : List (Round (sigN l.toComp.exports.length))} {cl : List (CRound sigU sigU)}
    (hN : cplay cl ∈ impNode (impSem P) l)
    (hA : twos (cl.flatMap (·.cs)) ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l))
    (hm : cl.map CRound.toRound = L.map Round.forget) : twos L ∈ l.toComp.den (impSem P) := by
  have hP : cplay (cl.map (CRound.inr (F₁ := sigU))) ∈
      (Strategy.id sigU).pair (impNode (impSem P) l) := cplay_pair_inr hN
  let upR : CRound sigU sigU → CRound sigU sigU :=
    fun r => ⟨(l.exp.exports.length + r.q.1, r.q.2), r.cs, r.a⟩
  have hS : cplay (cl.map upR) ∈ ((Strategy.id sigU).pair (impNode (impSem P) l)).comp
      (Strategy.ofHandler (splitH l.exp.exports.length)) :=
    cplay_comp_ofHandler (HC.of_map upR (CRound.inr (F₁ := sigU)) cl fun _ _ =>
      .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) hP
  have hE : cplay ((cl.map upR).map (CRound.hide (E := sigU))) ∈ envL (impSem P) l := by
    refine cplay_comp_serve ?_ hS
    rw [List.flatMap_map]
    exact hA
  rw [cplay_hide] at hE
  have e : ∀ (cl : List (CRound sigU sigU)) (L : List (Round (sigN l.toComp.exports.length))),
      cl.map CRound.toRound = L.map Round.forget →
      (cl.map upR).map CRound.toRound = L.map (shiftR l) := by
    intro cl
    induction cl with
    | nil =>
      intro L h
      cases L with
      | nil => rfl
      | cons _ _ => cases h
    | cons r cl ih =>
      intro L h
      cases L with
      | nil => cases h
      | cons x L =>
        simp only [List.map_cons, List.cons.injEq] at h ⊢
        refine ⟨?_, ih L h.2⟩
        obtain ⟨⟨q₁, q₂⟩, cs, a⟩ := r
        obtain ⟨⟨j, p⟩, b⟩ := x
        simp only [CRound.toRound, Round.forget, Sigma.mk.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, -⟩ := h
        cases ha
        rfl
  rw [e cl L hm] at hE
  have hU : twos (L.map Round.forget) ∈ l.toComp.denU (impSem P) := by
    rw [denU_toCompL]
    exact twos_comp_ofHandler (hrounds_shift l L) hE
  exact den_rounds (impSem P) l.toComp hU

end Top

/-! ## Ill-typed rounds of the linked denotation -/

section Den

variable {P : Profile} {l : Linked2}

theorem flatMap_filter_nil {E F : Sig.{0}} {p : CRound E F → Bool} :
    ∀ cl : List (CRound E F), (∀ r ∈ cl, p r = false → r.cs = []) →
      (cl.filter p).flatMap (·.cs) = cl.flatMap (·.cs)
  | [], _ => rfl
  | r :: cl, h => by
    have ih := flatMap_filter_nil cl fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    cases e : p r with
    | false =>
      rw [List.filter_cons_of_neg (by simp [e]), List.flatMap_cons, h r List.mem_cons_self e,
        List.nil_append, ih]
    | true => rw [List.filter_cons_of_pos e, List.flatMap_cons, List.flatMap_cons, ih]

theorem forall₂_of_map_eq' {α β : Type} {f : α → β} :
    ∀ {as : List α} {bs : List β}, as.map f = bs → List.Forall₂ (fun a b => f a = b) as bs
  | [], [], _ => .nil
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq' h.2)

theorem map_filter_eq {cl : List (CRound sigU sigU)}
    {L : List (Round (sigN l.toComp.exports.length))}
    (hm : cl.map CRound.toRound = L.map Round.forget) :
    (cl.filter fun r => good l r.q).map CRound.toRound =
      (L.filter fun x => good l (Round.forget x).1).map Round.forget := by
  have e₁ := List.filter_map (p := fun x : Round sigU => good l x.1) (f := CRound.toRound) (l := cl)
  have e₂ := List.filter_map (p := fun x : Round sigU => good l x.1) (f := Round.forget) (l := L)
  rw [hm] at e₁
  exact e₁.symm.trans e₂

/-- **Ill-typed rounds read back**: in a play of the linked denotation, an ill-typed question is
answered by a trap, a typed one by a trap or values, and the typed rounds alone are a play. -/
theorem den_inv (hc : l.imp.Good) {L : List (Round (sigN l.toComp.exports.length))}
    (h : twos L ∈ l.toComp.den (impSem P)) :
    (∀ x ∈ L.map Round.forget, good l x.1 = false → x.2 = none) ∧
    (∀ x ∈ L.map Round.forget, good l x.1 = true → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws)) ∧
    twos (L.filter fun x => good l (Round.forget x).1) ∈ l.toComp.den (impSem P) := by
  obtain ⟨cl, hN, hA, hm⟩ := den_top h
  obtain ⟨hbad, hgood, hF⟩ := impNode_inv hc hN
  have mem : ∀ x ∈ L.map Round.forget, ∃ r ∈ cl, r.q = x.1 ∧ r.a = x.2 := by
    intro x hx
    rw [← hm] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact ⟨r, hr, rfl, rfl⟩
  refine ⟨fun x hx hb => ?_, fun x hx hg => ?_, ?_⟩
  · obtain ⟨r, hr, hq, ha⟩ := mem x hx
    rw [← ha]
    exact (hbad r hr (by rw [hq]; exact hb)).2
  · obtain ⟨r, hr, hq, ha⟩ := mem x hx
    rw [← ha]
    exact hgood r hr (by rw [hq]; exact hg)
  · refine den_of_top hF ?_ (map_filter_eq hm)
    rw [flatMap_filter_nil cl fun r hr hb => (hbad r hr hb).1]
    exact hA

/-- **Ill-typed rounds inserted**: answered by a trap, into a play of the typed rounds. -/
theorem den_of (hc : l.imp.Good) {L : List (Round (sigN l.toComp.exports.length))}
    (hbad : ∀ x ∈ L.map Round.forget, good l x.1 = false → x.2 = none)
    (h : twos (L.filter fun x => good l (Round.forget x).1) ∈ l.toComp.den (impSem P)) :
    twos L ∈ l.toComp.den (impSem P) := by
  obtain ⟨cl', hN, hA, hm⟩ := den_top h
  have hm' : cl'.map CRound.toRound = (L.map Round.forget).filter fun x => good l x.1 := by
    rw [hm, List.filter_map]
    rfl
  obtain ⟨cl, F', e, hmem⟩ := forall₂_unfilter (R := fun c x => CRound.toRound c = x)
    (p := fun r : CRound sigU sigU => good l r.q) (p' := fun x : Round sigU => good l x.1)
    (fun x => ⟨x.1, [], x.2⟩) (fun c x hcx => by subst hcx; rfl) (L.map Round.forget) cl'
    (fun _ _ _ => rfl) (forall₂_of_map_eq' hm')
  have hcl : cl.map CRound.toRound = L.map Round.forget := forall₂_map_eq F'
  have hbad' : ∀ r ∈ cl, good l r.q = false → r.cs = [] ∧ r.a = none := by
    intro r hr hb
    obtain ⟨x, hx, rfl⟩ := hmem r hr hb
    exact ⟨rfl, hbad x hx hb⟩
  have hN' := impNode_of hc hbad' (by rw [e]; exact hN)
  refine den_of_top hN' ?_ hcl
  rw [← flatMap_filter_nil cl fun r hr hb => (hbad' r hr hb).1, e]
  exact hA

end Den

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv
