module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.Plays
public import Silmaril.Wasm.Component.Reference.LinkedSessionDivInv.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionFwd.Thms

/-!
# The injection of linked components into session objects

* `rounds_transferL`, `spec_transferL`, `div_rounds_transferL`, `divs_transferL`: specification
  sessions and divergences of two linked components with the same export types move along
  completed and divergent rounds of their triples, and conversely;
* `compSession_inj`: at the deterministic profiles, the reference-defined `Linked2.RefSessEquivD`
  is equality of the export types and of the session objects, through
  `StratSession.threadS_eq_iff` (store determinism, `storeDet_compTripleS`, and no plain traps)
  and #680's bisimulation from transfers (`SessionStrat.obsEq_of_transfer`); the divergence
  clause goes through `Linked2.RefSessEquivD.iff_sessDivs` (#730/#733's `sessDivs = refDivs`);
* `mem_inf_compSession`, `sessInf_iff`: the infinite plays are the coherent infinite sequences of
  terminating rounds, and for typed calls those whose every finite prefix is a reference session
  behaviour.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Rounds StoreDet roundsMoves roundMoves)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionStrat
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {prof : ProfileKind}

/-! ## Two linked components with the same export types -/

/-- The specification sessions of `l` from its instances' stores are sessions of `l'`. -/
def SpecSub (P : Profile) (l l' : Linked2) (len : l.imp.exports.length = l'.imp.exports.length)
    (Ie Ii Ie' Ii' : SInst) : Prop :=
  ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (u π : Store Nat), SimpleI.TypedCalls l.imp calls →
    Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u π →
    ∃ u' π', Linked2.SessSpec P l' Ie' Ii' Ii'.store Ie'.store (Linked2.castCalls len calls) outs
      u' π'

/-- The specification divergences of `l` are divergences of `l'`. -/
def DivSub (P : Profile) (l l' : Linked2) (len : l.imp.exports.length = l'.imp.exports.length) :
    Prop :=
  ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal), SimpleI.TypedCalls l.imp calls →
    ValTy.checkList l.imp.exports[j].ty.params vs = true →
    Linked2.sessDivs P l calls j vs ⊆ Linked2.sessDivs P l' (Linked2.castCalls len calls)
      (Fin.cast len j) vs

section Transfer

variable {l l' : Linked2} {len : l.imp.exports.length = l'.imp.exports.length}
  {Ie Ii Ie' Ii' : SInst}

theorem sessOutsL_castL (hty : SameTyL l l' len) :
    ∀ Lu : List (Round sigU), sessOutsL l' Lu = sessOutsL l Lu
  | [] => rfl
  | x :: Lu => by
    cases hq : l.typedQ x.1 with
    | none =>
      have hq' : l'.typedQ x.1 = none := by rw [typedQ_castL hty, hq]; rfl
      rw [sessOutsL_none hq, sessOutsL_none hq', sessOutsL_castL hty Lu]
    | some q =>
      have hq' : l'.typedQ x.1 = some (Fin.cast len q.1, q.2) := by
        rw [typedQ_castL hty, hq]; rfl
      rw [sessOutsL_some hq, sessOutsL_some hq', sessOutsL_castL hty Lu]

theorem shapedL_cast (hty : SameTyL l l' len) {Lu : List (Round sigU)} (h : ShapedL l Lu) :
    ShapedL l' Lu := by
  intro x hx
  obtain ⟨hn, hs⟩ := h x hx
  refine ⟨fun hq => hn ?_, fun q hq => ?_⟩
  · rw [typedQ_castL hty] at hq
    cases hq' : l.typedQ x.1 with
    | none => rfl
    | some _ => rw [hq'] at hq; cases hq
  · rw [typedQ_castL hty] at hq
    cases hq' : l.typedQ x.1 with
    | none => rw [hq'] at hq; cases hq
    | some r => exact hs r hq'

/-- Specification sessions move completed rounds. -/
theorem rounds_transferL (hty : SameTyL l l' len) (hsub : SpecSub P l l' len Ie Ii Ie' Ii')
    {rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))}
    {s : Store Nat × Store Nat}
    (h : Rounds (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store) rs s) :
    ∃ s', Rounds (Linked2.compTripleS P l' Ie' Ii') (Ie'.store, Ii'.store) rs s' := by
  obtain ⟨hspec, ht, hsh⟩ := spec_of_roundsL h
  obtain ⟨u', π', hspec'⟩ := hsub _ _ _ _ ht hspec
  rw [← sessCallsL_castL hty, ← sessOutsL_castL hty] at hspec'
  have hR := rounds_of_specL (shapedL_cast hty hsh) hspec'
  rw [map_ofRound_toRound] at hR
  exact ⟨_, hR⟩

/-- Completed rounds move specification sessions. -/
theorem spec_transferL (hty : SameTyL l l' len)
    (hR : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s,
      Rounds (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store) rs s →
      ∃ s', Rounds (Linked2.compTripleS P l' Ie' Ii') (Ie'.store, Ii'.store) rs s') :
    SpecSub P l l' len Ie Ii Ie' Ii' := by
  intro calls outs u π ht hspec
  obtain ⟨hR₀, e₁, e₂⟩ := rounds_of_sessSpecL hspec ht
  obtain ⟨s', hR'⟩ := hR _ _ hR₀
  obtain ⟨hspec', -, -⟩ := spec_of_roundsL hR'
  rw [map_toRound_ofRound, sessCallsL_castL hty, sessOutsL_castL hty, e₁, e₂] at hspec'
  exact ⟨_, _, hspec'⟩

/-- Specification divergences move divergent rounds. -/
theorem div_rounds_transferL (hty : SameTyL l l' len) (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) (hIe' : l'.exp.mod.IsInst Ie') (hIi' : l'.imp.mod.IsInst Ii')
    (hsub : DivSub P l l' len)
    {rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))}
    {s : Store Nat × Store Nat} {a : Nat × Payload} {c : List (Call (sigN 0))}
    (h : Rounds (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store) rs s)
    (hd : (c, End.div) ∈ (Linked2.compTripleS P l Ie Ii).1 s a) :
    ∃ s', Rounds (Linked2.compTripleS P l' Ie' Ii') (Ie'.store, Ii'.store) rs s' ∧
      (c, End.div) ∈ (Linked2.compTripleS P l' Ie' Ii').1 s' a := by
  obtain ⟨j, vs, hq, hdiv⟩ := div_iffL.mp hd
  obtain ⟨hspec, ht, hsh⟩ := spec_of_roundsL h
  obtain ⟨Ie'', Ii'', u', π', hIe'', hIi'', hspec', hdiv'⟩ :=
    hsub _ j vs ht (typedQ_some hq).2 ⟨Ie, Ii, s.2, s.1, hIe, hIi, hspec, hdiv⟩
  obtain rfl := NumModule.IsInst.unique hIe'' hIe'
  obtain rfl := ImpModule.IsInst.unique hIi'' hIi'
  rw [← sessCallsL_castL hty, ← sessOutsL_castL hty] at hspec'
  have hR := rounds_of_specL (shapedL_cast hty hsh) hspec'
  rw [map_ofRound_toRound] at hR
  refine ⟨_, hR, div_iffL.mpr ⟨Fin.cast len j, vs, ?_, hdiv'⟩⟩
  rw [typedQ_castL hty, hq]
  rfl

/-- Divergent rounds move specification divergences. -/
theorem divs_transferL (hty : SameTyL l l' len) (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) (hIe' : l'.exp.mod.IsInst Ie') (hIi' : l'.imp.mod.IsInst Ii')
    (hD : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s a c,
      Rounds (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store) rs s →
      (c, End.div) ∈ (Linked2.compTripleS P l Ie Ii).1 s a →
      ∃ s', Rounds (Linked2.compTripleS P l' Ie' Ii') (Ie'.store, Ii'.store) rs s' ∧
        (c, End.div) ∈ (Linked2.compTripleS P l' Ie' Ii').1 s' a) :
    DivSub P l l' len := by
  rintro calls j vs ht hv outs ⟨Ie'', Ii'', u, π, hIe'', hIi'', hspec, hdiv⟩
  obtain rfl := NumModule.IsInst.unique hIe'' hIe
  obtain rfl := ImpModule.IsInst.unique hIi'' hIi
  obtain ⟨hR, e₁, e₂⟩ := rounds_of_sessSpecL hspec ht
  have hq : l.typedQ (j.val, .vals vs) = some (j, vs) := typedQ_typed hv
  obtain ⟨s', hR', hd'⟩ := hD _ _ _ [] hR (div_iffL.mpr ⟨j, vs, hq, hdiv⟩)
  obtain ⟨j', vs', hq', hdiv'⟩ := div_iffL.mp hd'
  rw [typedQ_castL hty, hq] at hq'
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq'
  obtain ⟨rfl, rfl⟩ := hq'
  obtain ⟨hspec', -, -⟩ := spec_of_roundsL hR'
  rw [map_toRound_ofRound, sessCallsL_castL hty, sessOutsL_castL hty, e₁, e₂] at hspec'
  exact ⟨Ie', Ii', s'.2, s'.1, hIe', hIi', hspec', hdiv'⟩

/-- Reference session observations move specification sessions. -/
theorem specSub_of_obs (hl : l.Adequate) (hl' : l'.Adequate) (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) (hIe' : l'.exp.mod.IsInst Ie') (hIi' : l'.imp.mod.IsInst Ii')
    (hty : SameTyL l l' len) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (hobs : ∀ calls, SimpleI.TypedCalls l.imp calls →
      Linked2.sessObs prof l impl h₀ calls ⊆
        Linked2.sessObs prof l' impl h₀ (Linked2.castCalls len calls)) :
    SpecSub P l l' len Ie Ii Ie' Ii' := by
  intro calls outs u π ht hspec
  have href := hobs calls ht (Linked2.sess_specToRef P prof l hl impl h₀ hIe hIi hspec)
  rw [Linked2.sessObs_eq P prof l' hl' impl h₀ _ (typedCalls_castL hty ht) hIe' hIi'] at href
  obtain ⟨outs', u', π', hs, heq⟩ := href
  obtain rfl := refOuts_inj heq
  exact ⟨u', π', hs⟩

/-- Specification sessions move reference session observations. -/
theorem obs_of_specSub (hl : l.Adequate) (hl' : l'.Adequate) (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) (hIe' : l'.exp.mod.IsInst Ie') (hIi' : l'.imp.mod.IsInst Ii')
    (hty : SameTyL l l' len) (h : SpecSub P l l' len Ie Ii Ie' Ii')
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) :
    Linked2.sessObs prof l impl h₀ calls ⊆
      Linked2.sessObs prof l' impl h₀ (Linked2.castCalls len calls) := by
  rw [Linked2.sessObs_eq P prof l hl impl h₀ calls ht hIe hIi,
    Linked2.sessObs_eq P prof l' hl' impl h₀ _ (typedCalls_castL hty ht) hIe' hIi']
  rintro _ ⟨outs, u, π, hs, rfl⟩
  obtain ⟨u', π', hs'⟩ := h _ _ _ _ ht hs
  exact ⟨outs, u', π', hs', rfl⟩

theorem divSub_right (h : Linked2.RefSessEquiv P prof l l')
    (hdiv : ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
      (vs : List IVal), SimpleI.TypedCalls l.imp calls →
      ValTy.checkList l.imp.exports[j].ty.params vs = true →
      Linked2.sessDivs P l calls j vs =
        Linked2.sessDivs P l' (Linked2.castCalls h.len calls) (Fin.cast h.len j) vs) :
    DivSub P l' l h.len.symm := by
  intro calls' j' vs ht' hv'
  have ej : Fin.cast h.len (Fin.cast h.len.symm j') = j' := Fin.ext rfl
  have hv : ValTy.checkList l.imp.exports[Fin.cast h.len.symm j'].ty.params vs = true := by
    have e1 : l'.imp.exports[j'].ty = l.imp.exports[Fin.cast h.len.symm j'].ty :=
      h.ty (Fin.cast h.len.symm j')
    rw [← e1]
    exact hv'
  have e := hdiv (Linked2.castCalls h.len.symm calls') (Fin.cast h.len.symm j') vs
    (typedCalls_castL (sameTy_symmL h.ty) ht') hv
  rw [castCalls_castL h.len.symm calls', ej] at e
  exact e.symm.le

end Transfer

/-! ## The injection -/

/-- **The injection of adequate linked components into session objects**, at the deterministic
profiles. -/
theorem compSession_inj (o : GrowOracle) (prof : ProfileKind) {l l' : Linked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquivD (profile o) prof l l' ↔
      Linked2.SameTypes l l' ∧
        Linked2.compSession (profile o) l = Linked2.compSession (profile o) l' := by
  obtain ⟨Ie, hIe⟩ := hl.expInst.inst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨Ie', hIe'⟩ := hl'.expInst.inst
  obtain ⟨Ii', hIi'⟩ := hl'.impInst.inst
  rw [compSession_eq hIe hIi, compSession_eq hIe' hIi', Linked2.RefSessEquivD.iff_sessDivs hl hl']
  have hpend : ∀ s s', satP (Linked2.compTripleS (profile o) l Ie Ii) s =
      satP (Linked2.compTripleS (profile o) l' Ie' Ii') s' :=
    fun s s' => by funext a; rw [satP_compTripleS, satP_compTripleS]
  constructor
  · rintro ⟨h, hdiv⟩
    have hsub : SpecSub (profile o) l l' h.len Ie Ii Ie' Ii' :=
      specSub_of_obs (prof := prof) hl hl' hIe hIi hIe' hIi' h.ty
        (Silmaril.Wasm.Component.Canon.HostImpl.none (E := core3P (profile o)) (σ := Unit)) ()
        fun calls ht => (h.obs calls ht _ ()).le
    have hsub' : SpecSub (profile o) l' l h.len.symm Ie' Ii' Ie Ii :=
      specSub_of_obs (prof := prof) hl' hl hIe' hIi' hIe hIi (sameTy_symmL h.ty)
        (Silmaril.Wasm.Component.Canon.HostImpl.none (E := core3P (profile o)) (σ := Unit)) ()
        (obs_right h _ ())
    refine ⟨sameTypes_iffL.mpr ⟨h.len, h.ty⟩, StratSession.threadS_eq_of_obsEq
      (obsEq_of_transfer storeDet_compTripleS storeDet_compTripleS noPlainTrap_compTripleS
        noPlainTrap_compTripleS hpend (fun _ _ => rfl) ?_ ?_ ?_ ?_)⟩
    · exact fun rs s hr => rounds_transferL h.ty hsub hr
    · exact fun rs s hr => rounds_transferL (sameTy_symmL h.ty) hsub' hr
    · exact fun rs s a c hr hd => div_rounds_transferL h.ty hIe hIi hIe' hIi'
        (fun calls j vs ht hv => (hdiv calls j vs ht hv).le) hr hd
    · exact fun rs s a c hr hd => div_rounds_transferL (sameTy_symmL h.ty) hIe' hIi' hIe hIi
        (divSub_right (len := h.len) h hdiv) hr hd
  · rintro ⟨hst, heq⟩
    obtain ⟨len, hty⟩ := sameTypes_iffL.mp hst
    have hT := StratThread.threadT_eq_of_obsEq
      ((StratSession.threadS_eq_iff storeDet_compTripleS storeDet_compTripleS
        noPlainTrap_compTripleS noPlainTrap_compTripleS).mp heq)
    have hR : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s,
        Rounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store) rs s →
        ∃ s', Rounds (Linked2.compTripleS (profile o) l' Ie' Ii') (Ie'.store, Ii'.store) rs s' :=
      fun rs s h => StratThread.mem_rounds.mp (hT ▸ StratThread.mem_rounds.mpr ⟨s, h⟩)
    have hR' : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s,
        Rounds (Linked2.compTripleS (profile o) l' Ie' Ii') (Ie'.store, Ii'.store) rs s →
        ∃ s', Rounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store) rs s' :=
      fun rs s h => StratThread.mem_rounds.mp (hT.symm ▸ StratThread.mem_rounds.mpr ⟨s, h⟩)
    have hD : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s a c,
        Rounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store) rs s →
        (c, End.div) ∈ (Linked2.compTripleS (profile o) l Ie Ii).1 s a →
        ∃ s', Rounds (Linked2.compTripleS (profile o) l' Ie' Ii') (Ie'.store, Ii'.store) rs s' ∧
          (c, End.div) ∈ (Linked2.compTripleS (profile o) l' Ie' Ii').1 s' a :=
      fun rs s a c h hd => StratThread.mem_div.mp (hT ▸ StratThread.mem_div.mpr ⟨s, h, hd⟩)
    have hD' : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s a c,
        Rounds (Linked2.compTripleS (profile o) l' Ie' Ii') (Ie'.store, Ii'.store) rs s →
        (c, End.div) ∈ (Linked2.compTripleS (profile o) l' Ie' Ii').1 s a →
        ∃ s', Rounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store) rs s' ∧
          (c, End.div) ∈ (Linked2.compTripleS (profile o) l Ie Ii).1 s' a :=
      fun rs s a c h hd => StratThread.mem_div.mp (hT.symm ▸ StratThread.mem_div.mpr ⟨s, h, hd⟩)
    have hsub : SpecSub (profile o) l l' len Ie Ii Ie' Ii' := spec_transferL hty hR
    have hsub' : SpecSub (profile o) l' l len.symm Ie' Ii' Ie Ii :=
      spec_transferL (sameTy_symmL hty) hR'
    refine ⟨⟨len, hty, fun calls ht σ impl h₀ => Set.Subset.antisymm
      (obs_of_specSub hl hl' hIe hIi hIe' hIi' hty hsub calls ht impl h₀) ?_⟩,
      fun calls j vs ht hv => Set.Subset.antisymm
        (divs_transferL hty hIe hIi hIe' hIi' hD calls j vs ht hv) ?_⟩
    · have h := obs_of_specSub (prof := prof) hl' hl hIe' hIi' hIe hIi (sameTy_symmL hty) hsub'
        (Linked2.castCalls len calls) (typedCalls_castL hty ht) impl h₀
      rwa [castCalls_castL] at h
    · have ej : Fin.cast len.symm (Fin.cast len j) = j := Fin.ext rfl
      have h := divs_transferL (sameTy_symmL hty) hIe' hIi' hIe hIi hD'
        (Linked2.castCalls len calls) (Fin.cast len j) vs (typedCalls_castL hty ht)
        (by rw [hty]; exact hv)
      rwa [castCalls_castL, ej] at h

/-! ## Infinite plays -/

theorem mem_inf_compSession (o : GrowOracle) {l : Linked2} {Ie Ii : SInst}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {J : Set (List (Move (sigN 0) sessSig))} :
    J ∈ (Linked2.compSession (profile o) l).inf ↔
      ∃ a r s, StratThread.InfRounds (Linked2.compTripleS (profile o) l Ie Ii)
        (Ie.store, Ii.store) a r s ∧ J = StratSession.sroundsPlay a r := by
  rw [compSession_eq hIe hIi, StratSession.mem_inf_iff_of_storeDet storeDet_compTripleS]
  refine or_iff_right ?_
  rintro ⟨_, _, _, _, _, hω, _⟩
  simp [Linked2.compTripleS] at hω

theorem typed_streamTakeL {l : Linked2} {a : ℕ → Fin l.imp.exports.length × List IVal}
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) (n : ℕ) :
    SimpleI.TypedCalls l.imp (streamTake a n) := fun q hq => by
  simp only [streamTake, List.mem_ofFn] at hq
  obtain ⟨i, rfl⟩ := hq
  exact ht i

/-- **Coherent rounds from prefixes**: typed calls whose every finite prefix is a reference
session behaviour are a coherent infinite sequence of rounds (store determinism). -/
theorem infRounds_of_prefixL (prof : ProfileKind) {l : Linked2}
    (hl : l.Adequate) {Ie Ii : SInst} (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (hdet : StoreDet (Linked2.compTripleS P l Ie Ii))
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (h : ∀ k, refOuts (streamTake out k) ∈ Linked2.sessObs prof l impl h₀ (streamTake a k)) :
    ∃ s, StratThread.InfRounds (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store)
      (fun k => (((a k).1 : Nat), Payload.vals (a k).2)) (fun k => ([], outAns (out k))) s := by
  have hr : ∀ k, ∃ s, Rounds (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store)
      (streamTake (fun i => ((((a i).1 : Nat), Payload.vals (a i).2),
        (([] : List (Call (sigN 0))), outAns (out i)))) k) s := by
    intro k
    have hk := h k
    rw [Linked2.sessObs_eq _ prof l hl impl h₀ _ (typed_streamTakeL ht k) hIe hIi] at hk
    obtain ⟨outs, u, π, hspec, heq⟩ := hk
    obtain rfl := refOuts_inj heq
    obtain ⟨hR, -, -⟩ := rounds_of_sessSpecL hspec (typed_streamTakeL ht k)
    rw [← map_toRound_streamTake, map_ofRound_toRound] at hR
    exact ⟨_, hR⟩
  exact infRounds_of_rounds hdet hr

/-- **Infinite typed sessions**: the infinite play of typed calls answered by terminating
outcomes is an infinite play of the session object iff every finite prefix is a reference
session behaviour (under any host). -/
theorem sessInf_iff (o : GrowOracle) (prof : ProfileKind) {l : Linked2} (hl : l.Adequate)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    StratSession.sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => ([], outAns (out k))) ∈ (Linked2.compSession (profile o) l).inf ↔
      ∀ k, refOuts (streamTake out k) ∈ Linked2.sessObs prof l impl h₀ (streamTake a k) := by
  obtain ⟨Ie, hIe⟩ := hl.expInst.inst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  rw [compSession_eq hIe hIi]
  constructor
  · intro hJ k
    have hm := (StratSession.threadS (Linked2.compTripleS (profile o) l Ie Ii)
      (Ie.store, Ii.store)).inf_sub hJ ⟨k, List.prefix_refl _⟩
    obtain ⟨s, hR⟩ := (StratSession.mem_srounds_of_noPlainTrap noPlainTrap_compTripleS).mp hm
    obtain ⟨hspec, -, -⟩ := spec_of_roundsL hR
    rw [map_toRound_streamTake] at hspec
    have hlen : (streamTake a k).length = (streamTake out k).length := by simp [streamTake]
    obtain ⟨e₁, e₂⟩ := sessCallsL_sessLu (typed_streamTakeL ht k) hlen
    rw [e₁, e₂] at hspec
    exact Linked2.sess_specToRef _ prof l hl impl h₀ hIe hIi hspec
  · intro h
    obtain ⟨s, hs⟩ := infRounds_of_prefixL prof hl hIe hIi storeDet_compTripleS a out ht impl h₀ h
    exact StratSession.InfRounds.mem_sinf hs

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs
