module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Filter
import Silmaril.Wasm.Component.Reference.LinkedSessionAdeq.Thms

/-!
# The resumable-session equivalence of linked components

* `den_read`, `den_of_sess`: a play of complete rounds of the linked denotation is its typed
  session play (`Linked2.sessMoves`) with ill-typed rounds, answered by a trap, inserted;
* `linked2_sessEquiv_iff`: `Linked2.RefSessEquiv P prof l l'` holds exactly when `l` and `l'`
  have the same export types and the same IR plays at the untyped export interface (`pubPlays`).

The proof follows #676's `sessAdequacy`: the typed calls of a play are read back by #724's
`Linked2.sess_complete` and played by #705's `Linked2.sess_sound`; the ill-typed rounds depend on
the export types only (`Filter`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {prof : ProfileKind}

/-! ## Typed calls of rounds -/

/-- The typed calls of rounds. -/
def sessCallsL (l : Linked2) : List (Round sigU) → List (Fin l.imp.exports.length × List IVal)
  | [] => []
  | x :: L =>
    match l.typedQ x.1 with
    | some q => q :: sessCallsL l L
    | none => sessCallsL l L

/-- The outcomes of the typed calls of rounds. -/
def sessOutsL (l : Linked2) : List (Round sigU) → List (Option (List IVal))
  | [] => []
  | x :: L =>
    match l.typedQ x.1 with
    | some _ => SessionAdequacy.ansOut x.2 :: sessOutsL l L
    | none => sessOutsL l L

theorem sessCallsL_none {l : Linked2} {x : Round sigU} {L : List (Round sigU)}
    (h : l.typedQ x.1 = none) : sessCallsL l (x :: L) = sessCallsL l L := by
  simp [sessCallsL, h]

theorem sessCallsL_some {l : Linked2} {x : Round sigU} {L : List (Round sigU)}
    {q : Fin l.imp.exports.length × List IVal} (h : l.typedQ x.1 = some q) :
    sessCallsL l (x :: L) = q :: sessCallsL l L := by
  simp [sessCallsL, h]

theorem sessOutsL_none {l : Linked2} {x : Round sigU} {L : List (Round sigU)}
    (h : l.typedQ x.1 = none) : sessOutsL l (x :: L) = sessOutsL l L := by
  simp [sessOutsL, h]

theorem sessOutsL_some {l : Linked2} {x : Round sigU} {L : List (Round sigU)}
    {q : Fin l.imp.exports.length × List IVal} (h : l.typedQ x.1 = some q) :
    sessOutsL l (x :: L) = SessionAdequacy.ansOut x.2 :: sessOutsL l L := by
  simp [sessOutsL, h]

/-- **The typed rounds are a session**: their calls, typed, and their outcomes. -/
theorem read_filter (l : Linked2) : ∀ Lu : List (Round sigU),
    (∀ x ∈ Lu, good l x.1 = true → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws)) →
    Lu.filter (fun x => good l x.1) =
        SessionAdequacy.sessLu (sessCallsL l Lu) (sessOutsL l Lu) ∧
      (sessCallsL l Lu).length = (sessOutsL l Lu).length ∧
      SimpleI.TypedCalls l.imp (sessCallsL l Lu)
  | [], _ => ⟨rfl, rfl, fun _ h => nomatch h⟩
  | ⟨q, a⟩ :: Lu, h => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := read_filter l Lu fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases e : l.typedQ q with
    | none =>
      have hg : good l q = false := by simp [good, e]
      rw [List.filter_cons_of_neg (by simp [hg]), sessCallsL_none e, sessOutsL_none e]
      exact ⟨ih₁, ih₂, ih₃⟩
    | some jv =>
      obtain ⟨j, vs⟩ := jv
      have hg : good l q = true := by simp [good, e]
      rw [List.filter_cons_of_pos (by simp [hg]), sessCallsL_some e, sessOutsL_some e]
      obtain ⟨rfl, hck⟩ := typedQ_some e
      refine ⟨?_, by simp [ih₂], ?_⟩
      · rw [ih₁]
        rcases h _ List.mem_cons_self hg with ha | ⟨ws, ha⟩
        · have ha' : a = none := ha
          subst ha'
          rfl
        · have ha' : a = some (.vals ws) := ha
          subst ha'
          rfl
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hck
        · exact ih₃ x hx

theorem topRounds_forget (l : Linked2) :
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      (LinkedSessionAdeq.topRounds l calls outs).map Round.forget =
        SessionAdequacy.sessLu calls outs
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    show _ :: (LinkedSessionAdeq.topRounds l cs os).map Round.forget = _
    rw [topRounds_forget l cs os]
    rfl

/-! ## Plays of the linked denotation as sessions -/

section Plays

variable {l : Linked2}

/-- **A play of complete rounds read as a session**: its ill-typed rounds are answered by a
trap, and its typed rounds are the session play of their calls and outcomes. -/
theorem den_read (hc : l.imp.Good) {L : List (Round (sigN l.toComp.exports.length))}
    (h : twos L ∈ l.toComp.den (impSem P)) :
    (∀ x ∈ L.map Round.forget, good l x.1 = false → x.2 = none) ∧
    (L.map Round.forget).filter (fun x => good l x.1) =
      SessionAdequacy.sessLu (sessCallsL l (L.map Round.forget))
        (sessOutsL l (L.map Round.forget)) ∧
    (sessCallsL l (L.map Round.forget)).length = (sessOutsL l (L.map Round.forget)).length ∧
    SimpleI.TypedCalls l.imp (sessCallsL l (L.map Round.forget)) ∧
    Linked2.sessMoves l (sessCallsL l (L.map Round.forget)) (sessOutsL l (L.map Round.forget)) ∈
      l.toComp.den (impSem P) := by
  obtain ⟨hbad, hform, hF⟩ := den_inv hc h
  obtain ⟨e, hlen, ht⟩ := read_filter l (L.map Round.forget) hform
  refine ⟨hbad, e, hlen, ht, ?_⟩
  rw [LinkedSessionAdeq.sessMoves_eq]
  have he : L.filter (fun x => good l (Round.forget x).1) =
      LinkedSessionAdeq.topRounds l (sessCallsL l (L.map Round.forget))
        (sessOutsL l (L.map Round.forget)) := by
    apply forget_map_inj
    rw [topRounds_forget, ← e, List.filter_map]
    rfl
  rw [← he]
  exact hF

/-- **A session play with ill-typed rounds inserted** is a play of complete rounds. -/
theorem den_of_sess (hc : l.imp.Good) {L : List (Round (sigN l.toComp.exports.length))}
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (hbad : ∀ x ∈ L.map Round.forget, good l x.1 = false → x.2 = none)
    (e : (L.map Round.forget).filter (fun x => good l x.1) = SessionAdequacy.sessLu calls outs)
    (h : Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)) :
    twos L ∈ l.toComp.den (impSem P) := by
  rw [LinkedSessionAdeq.sessMoves_eq] at h
  refine den_of hc hbad ?_
  have he : L.filter (fun x => good l (Round.forget x).1) =
      LinkedSessionAdeq.topRounds l calls outs := by
    apply forget_map_inj
    rw [topRounds_forget, ← e, List.filter_map]
    rfl
  rw [he]
  exact h

/-- **Every play of the linked denotation is complete rounds, possibly followed by one pending
export question.** -/
theorem den_shape {p : List (Move (sigN 0) (sigN l.toComp.exports.length))}
    (hp : p ∈ l.toComp.den (impSem P)) :
    (∃ L, p = twos L) ∨ ∃ q L, p = twos L ++ [.inr (.ask q)] :=
  shape_of_legal ((l.toComp.den (impSem P)).legal hp) (noInl_sigN_nil rfl p)

end Plays

/-! ## Two linked components with the same export types -/

/-- The same export types, index by index. -/
def SameTyL (l l' : Linked2) (len : l.imp.exports.length = l'.imp.exports.length) : Prop :=
  ∀ j : Fin l.imp.exports.length, l'.imp.exports[Fin.cast len j].ty = l.imp.exports[j].ty

section Two

variable {l l' : Linked2} {len : l.imp.exports.length = l'.imp.exports.length}

theorem castCalls_castL (len : l.imp.exports.length = l'.imp.exports.length)
    (calls : List (Fin l.imp.exports.length × List IVal)) :
    Linked2.castCalls len.symm (Linked2.castCalls len calls) = calls := by
  simp only [Linked2.castCalls, List.map_map]
  conv_rhs => rw [← List.map_id calls]
  rfl

theorem sameTy_symmL (hty : SameTyL l l' len) : SameTyL l' l len.symm := by
  intro j'
  exact (hty (Fin.cast len.symm j')).symm

theorem sameTypes_iffL :
    Linked2.SameTypes l l' ↔ ∃ len : l.imp.exports.length = l'.imp.exports.length,
      SameTyL l l' len := by
  constructor
  · intro h
    have len : l.imp.exports.length = l'.imp.exports.length := by
      simpa using congrArg List.length h
    refine ⟨len, fun j => ?_⟩
    have := congrArg (fun x => x[j.val]?) h
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem j.isLt, List.getElem?_eq_getElem (len ▸ j.isLt)] at this
    simpa using this.symm
  · rintro ⟨len, hty⟩
    refine List.ext_getElem (by simp [len]) fun n h₁ h₂ => ?_
    simp only [List.getElem_map]
    exact (hty ⟨n, by simpa using h₁⟩).symm

theorem typedCalls_castL (hty : SameTyL l l' len)
    {calls : List (Fin l.imp.exports.length × List IVal)} (ht : SimpleI.TypedCalls l.imp calls) :
    SimpleI.TypedCalls l'.imp (Linked2.castCalls len calls) := by
  intro q hq
  obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
  show ValTy.checkList l'.imp.exports[Fin.cast len q₀.1].ty.params q₀.2 = true
  rw [hty]
  exact ht q₀ hq₀

theorem typedQ_castL (hty : SameTyL l l' len) (q : Nat × Payload) :
    l'.typedQ q = (l.typedQ q).map fun r => (Fin.cast len r.1, r.2) := by
  obtain ⟨j, p⟩ := q
  cases p with
  | flat _ => rfl
  | vals vs =>
    by_cases hj : j < l.imp.exports.length
    · have hj' : j < l'.imp.exports.length := len ▸ hj
      have e : l'.imp.exports[j].ty = l.imp.exports[j].ty := hty ⟨j, hj⟩
      cases hc : ValTy.checkList l.imp.exports[j].ty.params vs with
      | false =>
        have hc' : ValTy.checkList l'.imp.exports[j].ty.params vs = false := by rw [e]; exact hc
        simp [Linked2.typedQ, hj, hj', hc, hc']
      | true =>
        have hc' : ValTy.checkList l'.imp.exports[j].ty.params vs = true := by rw [e]; exact hc
        rw [typedQ_typed (j := ⟨j, hj⟩) hc, typedQ_typed (j := ⟨j, hj'⟩) hc']
        rfl
    · have hj' : ¬ j < l'.imp.exports.length := len ▸ hj
      simp [Linked2.typedQ, hj, hj']

theorem good_castL (hty : SameTyL l l' len) (q : Nat × Payload) : good l' q = good l q := by
  simp only [good, typedQ_castL hty q, Option.isSome_map]

theorem sessCallsL_castL (hty : SameTyL l l' len) :
    ∀ Lu : List (Round sigU), sessCallsL l' Lu = Linked2.castCalls len (sessCallsL l Lu)
  | [] => rfl
  | x :: Lu => by
    cases hq : l.typedQ x.1 with
    | none =>
      have hq' : l'.typedQ x.1 = none := by rw [typedQ_castL hty, hq]; rfl
      rw [sessCallsL_none hq, sessCallsL_none hq', sessCallsL_castL hty Lu]
    | some q =>
      have hq' : l'.typedQ x.1 = some (Fin.cast len q.1, q.2) := by
        rw [typedQ_castL hty, hq]; rfl
      rw [sessCallsL_some hq, sessCallsL_some hq', sessCallsL_castL hty Lu]
      rfl

theorem sessLu_castL : ∀ (calls : List (Fin l.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))),
    SessionAdequacy.sessLu (Linked2.castCalls len calls) outs = SessionAdequacy.sessLu calls outs
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    show _ :: SessionAdequacy.sessLu (Linked2.castCalls len cs) os = _ :: _
    rw [sessLu_castL cs os]
    rfl

end Two

/-! ## Adequacy -/

section Adequacy

variable {l l' : Linked2} {len : l.imp.exports.length = l'.imp.exports.length}

/-- **IR plays move along session observations.** -/
theorem pubPlays_subset (hl : l.Adequate) (hl' : l'.Adequate) (hty : SameTyL l l' len) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (hsub : ∀ calls, SimpleI.TypedCalls l.imp calls →
      Linked2.sessObs prof l impl h₀ calls ⊆
        Linked2.sessObs prof l' impl h₀ (Linked2.castCalls len calls)) :
    pubPlays (l.toComp.den (impSem P)) ⊆ pubPlays (l'.toComp.den (impSem P)) := by
  rintro _ ⟨p, hp, rfl⟩
  have hk : l.toComp.exports.length = l'.toComp.exports.length := by
    rw [Linked2.exports_length_toComp, Linked2.exports_length_toComp, len]
  have key : ∀ L : List (Round (sigN l.toComp.exports.length)),
      twos L ∈ l.toComp.den (impSem P) →
      ∃ L' : List (Round (sigN l'.toComp.exports.length)),
        twos L' ∈ l'.toComp.den (impSem P) ∧ L'.map Round.forget = L.map Round.forget := by
    intro L hL
    obtain ⟨hbad, e, hlen, ht, hmv⟩ := den_read hl.impGood hL
    have href := Linked2.sess_complete P prof l hl impl h₀ _ _ ht hlen hmv
    obtain ⟨outs', heq, -, hmv'⟩ := Linked2.sess_sound P prof l' hl' impl h₀ _
      (typedCalls_castL hty ht) (hsub _ ht href)
    obtain rfl := SessionAdequacy.refOuts_inj heq
    obtain ⟨L', hL'⟩ := SessionAdequacy.exists_forget (n := l'.toComp.exports.length)
      (L.map Round.forget) fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        rw [← hk]
        exact y.1.1.isLt
    refine ⟨L', den_of_sess hl'.impGood ?_ ?_ hmv', hL'⟩
    · rw [hL']
      intro x hx hb
      exact hbad x hx (by rw [← good_castL hty]; exact hb)
    · rw [hL', sessLu_castL, ← e]
      exact List.filter_congr fun x _ => good_castL hty x.1
  rcases den_shape hp with ⟨L, rfl⟩ | ⟨q, L, rfl⟩
  · obtain ⟨L', hL', he⟩ := key L hp
    exact ⟨twos L', hL', by rw [map_forgetMove_twos, map_forgetMove_twos, he]⟩
  · have hp₀ : twos L ∈ l.toComp.den (impSem P) :=
      (l.toComp.den (impSem P)).of_prefix hp (List.prefix_append _ _)
    obtain ⟨L', hL', he⟩ := key L hp₀
    let q' : (sigN l'.toComp.exports.length).Op := (⟨q.1.val, hk ▸ q.1.isLt⟩, q.2)
    refine ⟨twos L' ++ [.inr (.ask q')], ?_, ?_⟩
    · exact (l'.toComp.den (impSem P)).receptive hL' (path_twos _) (Step.ask q') trivial
    · rw [List.map_append, List.map_append, map_forgetMove_twos, map_forgetMove_twos, he]
      rfl

/-- **Session observations move along IR plays.** -/
theorem sessObs_subset (hl : l.Adequate) (hl' : l'.Adequate) (hty : SameTyL l l' len)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (hpl : pubPlays (l.toComp.den (impSem P)) ⊆ pubPlays (l'.toComp.den (impSem P)))
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls) :
    Linked2.sessObs prof l impl h₀ calls ⊆
      Linked2.sessObs prof l' impl h₀ (Linked2.castCalls len calls) := by
  intro o ho
  obtain ⟨outs, rfl, hlen, hmv⟩ := Linked2.sess_sound P prof l hl impl h₀ calls ht ho
  rw [LinkedSessionAdeq.sessMoves_eq] at hmv
  have hmv₀ : twos (E := sigN 0) (LinkedSessionAdeq.topRounds l calls outs) ∈
      l.toComp.den (impSem P) := hmv
  obtain ⟨p', hp', hpe⟩ := hpl ⟨_, hmv₀, rfl⟩
  rcases den_shape hp' with ⟨L', rfl⟩ | ⟨q, L', rfl⟩
  · rw [map_forgetMove_twos, map_forgetMove_twos, topRounds_forget] at hpe
    have hL : L' = LinkedSessionAdeq.topRounds l' (Linked2.castCalls len calls) outs := by
      apply forget_map_inj
      rw [twos_inj hpe, topRounds_forget, sessLu_castL]
    have hp'' : Linked2.sessMoves l' (Linked2.castCalls len calls) outs ∈
        l'.toComp.den (impSem P) := by
      rw [LinkedSessionAdeq.sessMoves_eq, ← hL]
      exact hp'
    exact Linked2.sess_complete P prof l' hl' impl h₀ _ outs (typedCalls_castL hty ht)
      (by simp [Linked2.castCalls, hlen]) hp''
  · exfalso
    rw [List.map_append, map_forgetMove_twos, map_forgetMove_twos] at hpe
    exact twos_ne_twos_ask _ _ _ hpe.symm

theorem obs_right (h : Linked2.RefSessEquiv P prof l l') {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) :
    ∀ calls', SimpleI.TypedCalls l'.imp calls' →
      Linked2.sessObs prof l' impl h₀ calls' ⊆
        Linked2.sessObs prof l impl h₀ (Linked2.castCalls h.len.symm calls') := by
  intro calls' ht'
  have e := h.obs (Linked2.castCalls h.len.symm calls')
    (typedCalls_castL (sameTy_symmL h.ty) ht') impl h₀
  rw [castCalls_castL h.len.symm calls'] at e
  exact e.symm.le

/-- **The resumable-session equivalence of linked components is IR play equality.** -/
theorem linked2_sessEquiv_iff (P : Profile) (prof : ProfileKind) (hl : l.Adequate)
    (hl' : l'.Adequate) :
    Linked2.RefSessEquiv P prof l l' ↔ Linked2.SameTypes l l' ∧
      pubPlays (l.toComp.den (impSem P)) = pubPlays (l'.toComp.den (impSem P)) := by
  constructor
  · intro h
    refine ⟨sameTypes_iffL.mpr ⟨h.len, h.ty⟩, Set.Subset.antisymm ?_ ?_⟩
    · exact pubPlays_subset hl hl' h.ty
        (Silmaril.Wasm.Component.Canon.HostImpl.none (E := core3P P) (σ := Unit)) ()
        fun calls ht => (h.obs calls ht _ ()).le
    · exact pubPlays_subset hl' hl (sameTy_symmL h.ty)
        (Silmaril.Wasm.Component.Canon.HostImpl.none (E := core3P P) (σ := Unit)) ()
        (obs_right h _ ())
  · rintro ⟨hst, heq⟩
    obtain ⟨len, hty⟩ := sameTypes_iffL.mp hst
    refine ⟨len, hty, fun calls ht σ impl h₀ => Set.Subset.antisymm
      (sessObs_subset hl hl' hty impl h₀ heq.le calls ht) ?_⟩
    have h := sessObs_subset (prof := prof) hl' hl (sameTy_symmL hty) impl h₀ heq.ge
      (Linked2.castCalls len calls) (typedCalls_castL hty ht)
    rwa [castCalls_castL] at h

end Adequacy

/-! ## The header forms -/

section Header

variable {l : Linked2}

theorem linked2_den_shape (P : Profile) (l : Linked2)
    {p : List (Move (sigN 0) (sigN l.toComp.exports.length))} (hp : p ∈ l.toComp.den (impSem P)) :
    (∃ L, p = exportRounds L) ∨ ∃ L q, p = exportRounds L ++ [.inr (.ask q)] := by
  rcases den_shape hp with ⟨L, rfl⟩ | ⟨q, L, rfl⟩
  · exact .inl ⟨L, (exportRounds_eq L).symm⟩
  · exact .inr ⟨L, q, by rw [exportRounds_eq]⟩

theorem linked2_den_filter_iff (P : Profile) (hi : l.imp.Good)
    (L : List (Σ q : (sigN l.toComp.exports.length).Op, (sigN l.toComp.exports.length).Ar q)) :
    exportRounds L ∈ l.toComp.den (impSem P) ↔
      (∀ x ∈ L, l.typedQ (x.1.1.val, x.1.2) = none → x.2 = none) ∧
      exportRounds (L.filter fun x => (l.typedQ (x.1.1.val, x.1.2)).isSome) ∈
        l.toComp.den (impSem P) := by
  rw [exportRounds_eq, exportRounds_eq]
  constructor
  · intro h
    obtain ⟨hbad, -, hF⟩ := den_inv hi h
    refine ⟨fun x hx hn => hbad (Round.forget x) (List.mem_map_of_mem hx) ?_, hF⟩
    simp only [good, Round.forget, hn, Option.isSome_none]
  · rintro ⟨hbad, hF⟩
    refine den_of hi (fun x hx hb => ?_) hF
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hbad y hy (good_false hb)

theorem linked2_den_answers (P : Profile) (hi : l.imp.Good)
    {L : List (Σ q : (sigN l.toComp.exports.length).Op, (sigN l.toComp.exports.length).Ar q)}
    (h : exportRounds L ∈ l.toComp.den (impSem P)) :
    ∀ x ∈ L, (l.typedQ (x.1.1.val, x.1.2)).isSome = true →
      x.2 = none ∨ ∃ ws, x.2 = some (.vals ws) := by
  rw [exportRounds_eq] at h
  obtain ⟨-, hgood, -⟩ := den_inv hi h
  exact fun x hx hg => hgood (Round.forget x) (List.mem_map_of_mem hx) hg

end Header

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv
