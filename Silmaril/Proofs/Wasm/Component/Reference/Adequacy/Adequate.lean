module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Main

/-!
# The finite adequacy theorem

`adequacy`: for adequate simple components (`Simple.Adequate`), `RefPubEquiv P prof c c'` holds
exactly when `c` and `c'` have the same export types and the same trap-last plays.

* `trapLastPlays_subset`: if every terminating public observation of `c` is one of `c'`, every
  trap-last play of `c` is one of `c'`. The play is read back as a chain of returned calls of the
  specification (`trapLast_read`), moved to `c'` through the reference machine
  (`chain_transfer`, `transfer_last`), and played again by `c'` (`seq_prefix`, `seqSpecToIR`,
  receptiveness for a pending question, the export handler for an ill-typed question).
* `obsSub_of_plays`: if every trap-last play of `c` is one of `c'`, every terminating public
  observation of `c` is one of `c'`: the observation is a play of `c` (soundness), hence of
  `c'`, which is read back (`read_back`) and run on the reference machine (`seq_specToRef`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {prof : ProfileKind}

/-! ## Interfaces -/

theorem castCalls_cast {c c' : Simple} (len : c.exports.length = c'.exports.length)
    (calls : List (Fin c.exports.length × List IVal)) :
    castCalls len.symm (castCalls len calls) = calls := by
  simp only [castCalls, List.map_map]
  conv_rhs => rw [← List.map_id calls]
  rfl

theorem sameTy_symm {c c' : Simple} {len : c.exports.length = c'.exports.length}
    (hty : SameTy c c' len) : SameTy c' c len.symm := by
  intro j'
  exact (hty (Fin.cast len.symm j')).symm

theorem sameTypes_iff {c c' : Simple} :
    SameTypes c c' ↔ ∃ len : c.exports.length = c'.exports.length, SameTy c c' len := by
  constructor
  · intro h
    have len : c.exports.length = c'.exports.length := by
      simpa using congrArg List.length h
    refine ⟨len, fun j => ?_⟩
    have := congrArg (fun l => l[j.val]?) h
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem j.isLt, List.getElem?_eq_getElem (len ▸ j.isLt)] at this
    simpa using this.symm
  · rintro ⟨len, hty⟩
    refine List.ext_getElem (by simp [len]) fun n h₁ h₂ => ?_
    simp only [List.getElem_map]
    exact (hty ⟨n, by simpa using h₁⟩).symm

/-! ## Plays of two components -/

theorem forget_seqMoves {c c' : Simple} (len : c.exports.length = c'.exports.length)
    (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal)) :
    (seqMoves c' (castCalls len calls) wss).map forgetMove =
      (seqMoves c calls wss).map forgetMove := by
  rw [seqMoves_eq, seqMoves_eq, map_forgetMove_twos, map_forgetMove_twos, seqRounds_forget,
    seqRounds_forget, castCalls_val]

theorem forget_last_twos (c : Simple) (calls : List (Fin c.exports.length × List IVal))
    (wss : List (List IVal)) (j : Nat) (hj : j < c.toComp.exports.length) (p : Payload)
    (A : Option Payload) :
    (twos (E := sigN 0) (seqRounds c calls wss ++
        ([⟨(⟨j, hj⟩, p), A⟩] : List (Round (sigN c.toComp.exports.length))))).map forgetMove =
      twos (seqRoundsU (calls.map fun q => (q.1.val, q.2)) wss ++
        ([⟨(j, p), A⟩] : List (Round sigU))) := by
  rw [map_forgetMove_twos, forget_last]

theorem seqMoves_last (c : Simple) (calls : List (Fin c.exports.length × List IVal))
    (wss : List (List IVal)) (q : (sigN c.toComp.exports.length).Op) (A : Option Payload) :
    seqMoves c calls wss ++ [.inr (.ask q), .inr (.ans q A)] =
      twos (E := sigN 0) (seqRounds c calls wss ++ [⟨q, A⟩]) := by
  rw [twos_append, seqMoves_eq]
  rfl

/-- **Trap-last plays move along public observations.** -/
theorem trapLastPlays_subset {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    {len : c.exports.length = c'.exports.length} (hty : SameTy c c' len)
    (hsub : ObsSub P prof c c' len) :
    trapLastPlays (c.toComp.den (modSem P)) ⊆ trapLastPlays (c'.toComp.den (modSem P)) := by
  rintro _ ⟨⟨p, hp, rfl⟩, htl⟩
  refine ⟨?_, htl⟩
  obtain ⟨I, hI⟩ := hc.inst.inst
  obtain ⟨calls, wss, s, ht, hlen, hseq, h⟩ := trapLast_read hc hI hp htl
  obtain ⟨I', s', hI', hseq'⟩ := chain_transfer (prof := prof) hc hc' hty hsub hI calls wss s ht
    hseq
  have hpre : seqMoves c' (castCalls len calls) wss ∈ c'.toComp.den (modSem P) :=
    seq_prefix hc'.good hI' hseq'
  have hk : c.toComp.exports.length = c'.toComp.exports.length := by
    rw [toComp_length, toComp_length, len]
  rcases h with rfl | ⟨q, rfl⟩ | ⟨q, s₂, rfl, hr⟩
  · exact ⟨_, hpre, forget_seqMoves len calls wss⟩
  · let q' : (sigN c'.toComp.exports.length).Op := (⟨q.1.val, hk ▸ q.1.isLt⟩, q.2)
    refine ⟨seqMoves c' (castCalls len calls) wss ++ [.inr (.ask q')], ?_, ?_⟩
    · have hpath : Path .idle (seqMoves c' (castCalls len calls) wss) .idle := by
        rw [seqMoves_eq]
        exact path_twos _
      exact (c'.toComp.den (modSem P)).receptive hpre hpath (Step.ask q') trivial
    · rw [List.map_append, List.map_append, forget_seqMoves len]
      rfl
  · obtain ⟨⟨j, hjk⟩, p⟩ := q
    have hj : j < c.exports.length := by rw [← toComp_length]; exact hjk
    have hj' : j < c'.toComp.exports.length := hk ▸ hjk
    rw [seqMoves_last, forget_last_twos]
    rcases hr with ⟨-, -, hn⟩ | ⟨hj₁, vs, xs, r, hp, hl, hr, hA, -⟩
    · -- a trap of the export handler
      have hq : exportsH c'.mod.exports.length c'.toComp.exports (j, p) = .pure none := by
        rcases exportsH_shape hc'.good (j, p) with ⟨he, -⟩ | ⟨hj'', vs, xs, hp, hl, -⟩
        · exact he
        · exfalso
          have hn' := hn hj vs hp
          have e : c'.exports[j].ty = c.exports[j].ty := hty ⟨j, hj⟩
          simp only [e, hn'] at hl
          cases hl
      obtain ⟨-, -, li₀, lc₀, hact, H₀, X₀⟩ := seq_rounds hc'.good hI' (castCalls len calls) wss
        I'.store s' hI'.1.choose_spec.ok hseq'
      have hden := seq_den (P := P) (U := [⟨(⟨j, hj'⟩, p), none⟩]) (li := []) (lc := []) hI' hact
        (I'.strategy P s').nil_mem H₀ .nil X₀ (.pure hq .nil)
      refine ⟨_, hden, (forget_last_twos c' (castCalls len calls) wss j hj' p none).trans ?_⟩
      rw [castCalls_val]
    · -- a trap of the core activation or of the lift
      obtain rfl := hp
      have hvs : ValTy.checkList c.exports[j].ty.params vs = true := (checkLower_eq hl).1
      have hb : ObsAns (liftOutcome c.exports[j].ty r) none := hA ▸ obsAns_liftOutcome _ r
      have hbt : liftOutcome c.exports[j].ty r = .traps := obsAns_unique hb rfl
      have hspec : Silmaril.Wasm.Component.Reference.Outcome.traps ∈
          specAt P c I c.exports[(⟨j, hj⟩ : Fin c.exports.length)] vs s := by
        have hl' : checkLower c.exports[(⟨j, hj⟩ : Fin c.exports.length)].ty.params vs =
            some xs := hl
        have hr' : r ∈ coreAt P I c.exports[(⟨j, hj⟩ : Fin c.exports.length)].core xs s := hr
        rw [← hbt]
        unfold specAt
        rw [hl']
        exact .inl ⟨r, hr', rfl⟩
      obtain ⟨I'', s'', hI'', hseq'', hb''⟩ := transfer_last (prof := prof) hc hc' hty hsub hI ht
        hseq hvs hspec trivial
      have hir := seqSpecToIR P c' hc'.good I'' hI'' (castCalls len calls) wss s''
        (Fin.cast len ⟨j, hj⟩) vs .traps hseq'' hb''
      refine ⟨_, hir, ?_⟩
      have e₁ := seqMoves_last c' (castCalls len calls) wss (⟨j, hj'⟩, .vals vs) none
      have e₂ := forget_last_twos c' (castCalls len calls) wss j hj' (.vals vs) none
      rw [castCalls_val] at e₂
      exact (congrArg (List.map forgetMove) e₁).trans e₂

/-- **Public observations move along trap-last plays.** -/
theorem obsSub_of_plays {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    {len : c.exports.length = c'.exports.length} (hty : SameTy c c' len)
    (hpl : trapLastPlays (c.toComp.den (modSem P)) ⊆ trapLastPlays (c'.toComp.den (modSem P))) :
    ObsSub P prof c c' len := by
  intro calls j vs ht hvs p ⟨hp, hterm⟩
  obtain ⟨I, wss, s, hI, hseq, hp1, hb⟩ := seq_refToSpec P prof c hc.good hc.floatFree hc.inst
    hc.arity calls j vs ht hvs p hp
  obtain ⟨-, hlen, -⟩ := seq_rounds hc.good hI calls wss I.store s hI.1.choose_spec.ok hseq
  have hir := seqSpecToIR P c hc.good I hI calls wss s j vs p.2 hseq hb
  have hjk : j.val < c.toComp.exports.length := by rw [toComp_length]; exact j.isLt
  obtain ⟨A, hA, hL⟩ : ∃ A, ObsAns p.2 A ∧
      twos (E := sigN 0) (seqRounds c calls wss ++ [⟨(⟨j.val, hjk⟩, .vals vs), A⟩]) ∈
        c.toComp.den (modSem P) := by
    obtain ⟨p1, b⟩ := p
    cases b with
    | returns r =>
      cases r with
      | none => exact hterm.elim
      | some rs =>
        obtain ⟨ws, rfl, h⟩ := hir
        rw [seqMoves_eq, seqRounds_append c j vs ws calls wss hlen] at h
        exact ⟨_, ⟨ws, rfl, rfl⟩, h⟩
    | traps =>
      refine ⟨none, rfl, ?_⟩
      rw [← seqMoves_last]
      exact hir
    | deadlocks => exact hterm.elim
    | diverges => exact hterm.elim
  have hmem : (twos (E := sigN 0)
      (seqRounds c calls wss ++ [⟨(⟨j.val, hjk⟩, .vals vs), A⟩])).map forgetMove ∈
        trapLastPlays (c.toComp.den (modSem P)) := by
    refine ⟨⟨_, hL, rfl⟩, ?_⟩
    rw [forget_last_twos]
    exact trapLast_twos_last _ (seqRoundsU_allSome _ _)
  obtain ⟨⟨p'', hp'', he⟩, -⟩ := hpl hmem
  obtain ⟨I', hI'⟩ := hc'.inst.inst
  rw [forget_last_twos] at he
  rcases den_shape _ c' hp'' with ⟨L'', rfl⟩ | ⟨q, L'', rfl⟩
  · rw [map_forgetMove_twos] at he
    have hvs' : ValTy.checkList c'.exports[j.val].ty.params vs = true := by
      have e : c'.exports[j.val].ty = c.exports[j].ty := hty j
      rw [e]
      exact hvs
    obtain ⟨calls', s', b', hc₁, ht', hseq', hb', hspec'⟩ := read_back hc' hI' hp''
      (by rw [List.length_map]; exact hlen) (twos_inj he) (len ▸ j.isLt) hvs'
    have e₁ : calls' = castCalls len calls :=
      calls_eq_of_val (hc₁.trans (castCalls_val len calls).symm)
    subst e₁
    have e₂ := obsAns_unique hA hb'
    have href := seq_specToRef P prof c' hc'.good hc'.floatFree hc'.inst hc'.arity hI'
      (castCalls len calls) wss s' (Fin.cast len j) vs ht' hvs' hseq' hspec' (e₂ ▸ hterm)
    refine ⟨?_, hterm⟩
    obtain ⟨p1, b⟩ := p
    simp only at hp1 e₂
    rw [hp1, e₂]
    exact href
  · exfalso
    rw [List.map_append, map_forgetMove_twos] at he
    exact twos_ne_twos_ask _ _ _ he.symm

/-! ## The theorem -/

theorem obsSub_left {c c' : Simple} (h : RefPubEquiv P prof c c') : ObsSub P prof c c' h.len :=
  fun calls j vs ht hvs => (h.obs calls j vs ht hvs).le

theorem obsSub_right {c c' : Simple} (h : RefPubEquiv P prof c c') :
    ObsSub P prof c' c h.len.symm := by
  intro calls' j' vs ht' hvs'
  have hvs : ValTy.checkList c.exports[Fin.cast h.len.symm j'].ty.params vs = true := by
    rw [sameTy_symm h.ty j']
    exact hvs'
  have e := h.obs (castCalls h.len.symm calls') (Fin.cast h.len.symm j') vs
    (typedCalls_cast (sameTy_symm h.ty) ht') hvs
  have e₁ : castCalls h.len (castCalls h.len.symm calls') = calls' := castCalls_cast h.len.symm calls'
  have e₂ : Fin.cast h.len (Fin.cast h.len.symm j') = j' := Fin.ext rfl
  rw [e₁, e₂] at e
  exact e.symm.le

/-- **Finite adequacy**: for adequate simple components, the public component interaction
equivalence on the reference machine is equality of export types and of trap-last IR plays. -/
theorem adequacy (P : Profile) (prof : ProfileKind) {c c' : Simple} (hc : c.Adequate)
    (hc' : c'.Adequate) :
    RefPubEquiv P prof c c' ↔ SameTypes c c' ∧
      trapLastPlays (c.toComp.den (modSem P)) = trapLastPlays (c'.toComp.den (modSem P)) := by
  constructor
  · intro h
    refine ⟨sameTypes_iff.mpr ⟨h.len, h.ty⟩, Set.Subset.antisymm ?_ ?_⟩
    · exact trapLastPlays_subset hc hc' h.ty (obsSub_left h)
    · exact trapLastPlays_subset hc' hc (sameTy_symm h.ty) (obsSub_right h)
  · rintro ⟨hst, heq⟩
    obtain ⟨len, hty⟩ := sameTypes_iff.mp hst
    refine ⟨len, hty, fun calls j vs ht hvs => Set.Subset.antisymm
      (obsSub_of_plays hc hc' hty heq.le calls j vs ht hvs) ?_⟩
    have hvs' : ValTy.checkList c'.exports[Fin.cast len j].ty.params vs = true := by
      rw [hty]
      exact hvs
    have h := obsSub_of_plays (prof := prof) hc' hc (sameTy_symm hty) heq.ge (castCalls len calls)
      (Fin.cast len j) vs (typedCalls_cast hty ht) hvs'
    have e₁ : castCalls len.symm (castCalls len calls) = calls := castCalls_cast len calls
    have e₂ : Fin.cast len.symm (Fin.cast len j) = j := Fin.ext rfl
    rw [e₁, e₂] at h
    exact h

/-! ## Completeness for one call -/

/-- **Completeness for one call**: every IR play of a call with a terminating answer, as `IRObs`
prescribes, is a reference behaviour of the call after instantiation. -/
theorem complete (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Silmaril.Wasm.Component.Reference.Outcome) (hterm : b.Term)
    (hb : IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b) :
    b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal) := by
  have hs : SeqIRObs c (c.toComp.den (modSem P)) [] [] j vs b := by
    cases b with
    | returns r =>
      cases r with
      | none => exact hterm.elim
      | some rs => exact hb
    | traps => exact hb
    | deadlocks => exact hterm.elim
    | diverges => exact hterm.elim
  obtain ⟨-, h⟩ := complete_seq P prof c hc [] [] rfl j vs hvs b hterm hs
  rcases h with ⟨m₀, inst, es, fs, mₙ, f, hr, -, hS, hl, hb₀⟩ | ⟨he, hr⟩ | ⟨he, hr⟩
  · simp only [List.map_nil, List.zip_nil_right] at hS
    cases hS
    exact .inl ⟨m₀, inst, es, f, hr, hl, hb₀⟩
  · exact .inr (.inl ⟨(Prod.mk.inj he).2, hr⟩)
  · exact .inr (.inr ⟨(Prod.mk.inj he).2, hr⟩)

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
