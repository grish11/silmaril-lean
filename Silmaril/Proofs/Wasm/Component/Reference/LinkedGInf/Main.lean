module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.Ref
public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Thms

/-!
# Infinite plays and the full injection of linked components and chains

* `inf_iff_stream`: for an exporter meeting `Adeq`, `AdeqI` and `Det`, the infinite IR play of a
  typed stream of rounds is a run of them from the initial state (`AdeqI` one way; the prefixes
  are finite plays, `Adeq.bwd`, whose runs cohere, `stream_run_of_det`, the other);
* `inf_iff_runG`, `refSessProd_iff_runG`, `inf_iff_profileG`: for a link meeting `ProfOk` at
  `profile o`, the infinite IR plays of typed call streams, the runs of `g.toExp Ii` and the
  productive executions agree;
* `sessObs_eq_irG`, `quiet_iffG`: the terminating session outcomes are the typed finite IR plays
  (`LinkedG.sessObs_eqUX`, `toExp_adeq`), the quiescent divergences the IR divergences
  (`LinkedG.sessDivs_eq_refDivs`, `LinkedG.div_iff_sessDivs`, `toExp_adeqD_profile`);
* `refSessEquivFull_iffG`: the full injection;
* `extOk_profOk`: one more importer on a chain with a simple base meets `ProfOk`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy (refOuts_inj)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy Payload)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## An exporter: infinite plays are runs -/

theorem typed_streamTakeR {e : ExpSpec} {r : ℕ → URound} (ht : ∀ k, e.Typed (r k)) (n : ℕ) :
    ∀ x ∈ streamTake r n, e.Typed x := by
  intro x hx
  simp only [streamTake, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ht i

/-- **The infinite IR plays of a typed stream of rounds are its runs**, for a deterministic
exporter meeting `Adeq` and `AdeqI`. -/
theorem inf_iff_stream {P : Profile} {e : ExpSpec} (he : e.Adeq P) (hI : e.AdeqI P)
    (hd : e.Det P) (r : ℕ → URound) (ht : ∀ k, e.Typed (r k)) :
    Chain.lim (fun n => uMoves (streamTake r n)) ∈ (e.comp.denUD (impSemD P)).inf ↔
      ∃ S : ℕ → e.St, S 0 = e.init ∧ ∀ k, e.Step P (S k) (r k) (S (k + 1)) := by
  constructor
  · intro hJ
    refine stream_run_of_det hd r e.init fun n => he.bwd _ (typed_streamTakeR ht n) ?_
    have hm := (e.comp.denUD (impSemD P)).inf_sub hJ (Chain.mem_lim_self _ n)
    rw [toStrategy_denUD_impSemD] at hm
    exact hm
  · rintro ⟨S, h0, hS⟩
    exact hI r S h0 hS

/-! ## A linked component -/

section Linked

variable {g : LinkedG}

theorem typed_roundU {Ii : SInst} {a : ℕ → Fin g.imp.exports.length × List IVal}
    {out : ℕ → Option (List IVal)}
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) (k : ℕ) :
    (g.toExp Ii).Typed (g.roundU a out k) := by
  have hlt : (a k).1.val < g.toComp.exports.length :=
    (LinkedG.exports_length_toComp g).symm ▸ (a k).1.isLt
  refine ⟨⟨(a k).1.val, hlt⟩, (a k).2, rfl, ?_⟩
  show ValTy.checkList g.toComp.exports[(a k).1.val].ty.params (a k).2 = true
  rw [LinkedG.toComp_ty g hlt (a k).1.isLt]
  exact ht k

theorem typed_sessU {Ii : SInst} {calls : List (Fin g.imp.exports.length × List IVal)}
    (ht : SimpleI.TypedCalls g.imp calls) (outs : List (Option (List IVal))) :
    ∀ r ∈ g.sessU calls outs, (g.toExp Ii).Typed r := by
  intro r hr
  obtain ⟨co, hco, rfl⟩ := List.mem_map.mp hr
  have hlt : co.1.1.val < g.toComp.exports.length :=
    (LinkedG.exports_length_toComp g).symm ▸ co.1.1.isLt
  refine ⟨⟨co.1.1.val, hlt⟩, co.1.2, rfl, ?_⟩
  show ValTy.checkList g.toComp.exports[co.1.1.val].ty.params co.1.2 = true
  rw [LinkedG.toComp_ty g hlt co.1.1.isLt]
  exact ht _ (List.of_mem_zip hco).1

variable {o : GrowOracle} {prof : ProfileKind}

/-- **The infinite IR plays of typed call streams are the runs of `g.toExp Ii`.** -/
theorem inf_iff_runG (hg : g.ProfOk o) {Ii : SInst} (hI : g.imp.mod.IsInst Ii)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) :
    g.sessInfU a out ∈ (g.toComp.denUD (impSemD (profile o))).inf ↔
      ∃ S : ℕ → (g.toExp Ii).St, S 0 = (g.toExp Ii).init ∧
        ∀ k, (g.toExp Ii).Step (profile o) (S k) (g.roundU a out k) (S (k + 1)) :=
  inf_iff_stream (LinkedG.toExp_adeq hg.adeq hg.link.good hI hg.link.wireTy)
    (LinkedG.toExp_adeqI hg.adeq hg.adeqI hg.link.good hI) (LinkedG.toExp_det hg.det) _
    (typed_roundU ht)

/-- **The productive executions of typed call streams are the runs of `g.toExp Ii`.** -/
theorem refSessProd_iff_runG (hg : g.ProfOk o) {Ii : SInst} (hI : g.imp.mod.IsInst Ii)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    LinkedG.RefSessProd (profile o) prof g impl h₀ a out ↔
      ∃ S : ℕ → (g.toExp Ii).St, S 0 = (g.toExp Ii).init ∧
        ∀ k, (g.toExp Ii).Step (profile o) (S k) (g.roundU a out k) (S (k + 1)) :=
  ⟨run_of_refSessProd hg.ref.refAdeqUX hg.link hI (LinkedG.toExp_det hg.det) a out ht,
    fun ⟨_, h0, hS⟩ => refSessProd_of_run hg.ref.refAdeqUX hg.link hI impl h₀ a out h0 hS⟩

/-- **Productive executions are their finite prefixes.** -/
theorem refSessProd_iff_prefixG (hg : g.ProfOk o)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    LinkedG.RefSessProd (profile o) prof g impl h₀ a out ↔
      ∀ n, refOuts (streamTake out n) ∈ LinkedG.sessObs prof g impl h₀ (streamTake a n) := by
  obtain ⟨Ii, hI⟩ := hg.link.inst.inst
  refine ⟨refSessProd_prefixG, fun h => ?_⟩
  obtain ⟨_, h0, hS⟩ := run_of_prefix hg.ref.refAdeqUX hg.link hI (LinkedG.toExp_det hg.det) a
    out ht impl h₀ h
  exact refSessProd_of_run hg.ref.refAdeqUX hg.link hI impl h₀ a out h0 hS

/-- **The infinite IR plays of typed call streams are the productive executions.** -/
theorem inf_iff_profileG (hg : g.ProfOk o) (a : ℕ → Fin g.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    g.sessInfU a out ∈ (g.toComp.denUD (impSemD (profile o))).inf ↔
      LinkedG.RefSessProd (profile o) prof g impl h₀ a out := by
  obtain ⟨Ii, hI⟩ := hg.link.inst.inst
  exact (inf_iff_runG hg hI a out ht).trans (refSessProd_iff_runG hg hI a out ht impl h₀).symm

/-! ### Finite plays and divergences -/

/-- **The terminating session outcomes are the typed finite IR plays.** -/
theorem sessObs_eq_irG (hg : g.ProfOk o) {σ : Type} (impl : HostImpl (core3P (profile o)) σ)
    (h₀ : σ) (calls : List (Fin g.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls g.imp calls) :
    LinkedG.sessObs prof g impl h₀ calls =
      {x | ∃ outs, x = refOuts outs ∧ calls.length = outs.length ∧
        uMoves (g.sessU calls outs) ∈ (g.toComp.denUD (impSemD (profile o))).toStrategy} := by
  obtain ⟨Ii, hI⟩ := hg.link.inst.inst
  have hA := LinkedG.toExp_adeq hg.adeq hg.link.good hI hg.link.wireTy
  rw [LinkedG.sessObs_eqUX (profile o) prof hg.ref.refAdeqUX hg.link.wireTy hg.link.nodup
    hg.link.good hg.link.inst hg.link.arity hg.link.floats hg.link.split hg.link.names impl h₀
    calls ht hI, toStrategy_denUD_impSemD]
  ext x
  constructor
  · rintro ⟨outs, u', s', hspec, rfl⟩
    exact ⟨outs, rfl, LinkedG.sessSpec_lengthG hspec, hA.fwd _ _ (run_of_sessSpec hspec)⟩
  · rintro ⟨outs, rfl, hlen, hm⟩
    obtain ⟨s, hs⟩ := hA.bwd _ (typed_sessU ht outs) hm
    obtain ⟨ds, hOk, hp, hr, hmm⟩ := LinkedG.rounds_of_run hs
    exact ⟨outs, s.1, s.2, LinkedGDivIR.sessSpec_of_idleG ds calls outs hmm hlen hOk hp hr, rfl⟩

theorem mem_ir_iffG (hg : g.ProfOk o) {σ : Type} (impl : HostImpl (core3P (profile o)) σ)
    (h₀ : σ) {calls : List (Fin g.imp.exports.length × List IVal)}
    (ht : SimpleI.TypedCalls g.imp calls) {outs : List (Option (List IVal))}
    (hlen : calls.length = outs.length) :
    uMoves (g.sessU calls outs) ∈ (g.toComp.denUD (impSemD (profile o))).toStrategy ↔
      refOuts outs ∈ LinkedG.sessObs prof g impl h₀ calls := by
  rw [sessObs_eq_irG hg impl h₀ calls ht]
  constructor
  · intro hm
    exact ⟨outs, rfl, hlen, hm⟩
  · rintro ⟨outs', e, -, hm⟩
    obtain rfl := refOuts_inj e
    exact hm

theorem sessDivs_lengthG {P : Profile} {Ii : SInst}
    {calls : List (Fin g.imp.exports.length × List IVal)} {j : Fin g.imp.exports.length}
    {vs : List IVal} {outs : List (Option (List IVal))}
    (h : outs ∈ LinkedG.sessDivs P g Ii calls j vs) : calls.length = outs.length := by
  obtain ⟨_, _, hS, _⟩ := h
  exact LinkedG.sessSpec_lengthG hS

/-- **The quiescent divergences are the IR divergences after typed sessions.** -/
theorem quiet_iffG (hg : g.ProfOk o) {σ : Type} (impl : HostImpl (core3P (profile o)) σ)
    (h₀ : σ) (calls : List (Fin g.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))) (j : Fin g.imp.exports.length) (vs : List IVal)
    (ht : SimpleI.TypedCalls g.imp calls)
    (hvs : ValTy.checkList g.imp.exports[j].ty.params vs = true) :
    LinkedG.RefSessQuiet (profile o) prof g impl h₀ calls outs j vs ↔
      calls.length = outs.length ∧ uMoves (g.sessU calls outs) ++ [.inr (.ask (j.val, .vals vs))] ∈
        (g.toComp.denUD (impSemD (profile o))).div := by
  obtain ⟨Ii, hI⟩ := hg.link.inst.inst
  have hA := LinkedG.toExp_adeqD_profile hg.adeq hg.adeqD hg.adeqI
    (ExpSpec.adeqIC_of_det hg.adeq hg.det) hg.link.good hI hg.link.wireTy
  have e := LinkedG.sessDivs_eq_refDivs (profile o) prof hg.ref hg.link impl h₀ calls j vs ht hvs hI
  change outs ∈ LinkedG.refDivs (profile o) prof g impl h₀ calls j vs ↔ _
  rw [← e]
  constructor
  · intro h
    exact ⟨sessDivs_lengthG h, (LinkedG.div_iff_sessDivs hA ht (sessDivs_lengthG h) hvs).2 h⟩
  · rintro ⟨hlen, h⟩
    exact (LinkedG.div_iff_sessDivs hA ht hlen hvs).1 h

/-! ### The full injection -/

theorem sameTypes_iffG {g' : LinkedG} :
    LinkedG.SameTypes g g' ↔ ∃ len : g.imp.exports.length = g'.imp.exports.length,
      ∀ j : Fin g.imp.exports.length, g'.imp.exports[Fin.cast len j].ty = g.imp.exports[j].ty := by
  constructor
  · intro h
    have len : g.imp.exports.length = g'.imp.exports.length := by
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

theorem typedCalls_castG {g' : LinkedG} {len : g.imp.exports.length = g'.imp.exports.length}
    (hty : ∀ j : Fin g.imp.exports.length, g'.imp.exports[Fin.cast len j].ty = g.imp.exports[j].ty)
    {calls : List (Fin g.imp.exports.length × List IVal)} (ht : SimpleI.TypedCalls g.imp calls) :
    SimpleI.TypedCalls g'.imp (LinkedG.castCalls len calls) := by
  intro q hq
  obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
  show ValTy.checkList g'.imp.exports[Fin.cast len q₀.1].ty.params q₀.2 = true
  rw [hty]
  exact ht q₀ hq₀

theorem typed_castStreamG {g' : LinkedG} {len : g.imp.exports.length = g'.imp.exports.length}
    (hty : ∀ j : Fin g.imp.exports.length, g'.imp.exports[Fin.cast len j].ty = g.imp.exports[j].ty)
    {a : ℕ → Fin g.imp.exports.length × List IVal}
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) :
    ∀ k, ValTy.checkList g'.imp.exports[(LinkedG.castStream len a k).1].ty.params
      (LinkedG.castStream len a k).2 = true := fun k => by
  show ValTy.checkList g'.imp.exports[Fin.cast len (a k).1].ty.params (a k).2 = true
  rw [hty]
  exact ht k

theorem length_castCallsG {g' : LinkedG} (len : g.imp.exports.length = g'.imp.exports.length)
    (calls : List (Fin g.imp.exports.length × List IVal)) :
    (LinkedG.castCalls len calls).length = calls.length := by
  simp [LinkedG.castCalls]

/-- **The full injection of the IR** at `profile o`. -/
theorem refSessEquivFull_iffG {g' : LinkedG} (hg : g.ProfOk o) (hg' : g'.ProfOk o) :
    LinkedG.RefSessEquivFull (profile o) prof g g' ↔ LinkedG.SameTypes g g' ∧
      LinkedG.IRFinEq (profile o) g g' ∧ LinkedG.IRDivEq (profile o) g g' ∧
      LinkedG.IRInfEq (profile o) g g' := by
  constructor
  · intro h
    refine ⟨sameTypes_iffG.2 ⟨h.len, h.ty⟩, ⟨h.len, fun calls outs ht hlen => ?_⟩,
      ⟨h.len, fun calls outs j vs ht hlen hvs => ?_⟩, ⟨h.len, fun a out ht => ?_⟩⟩
    · have ht' := typedCalls_castG h.ty ht
      have hlen' : (LinkedG.castCalls h.len calls).length = outs.length := by
        rw [length_castCallsG]
        exact hlen
      rw [mem_ir_iffG hg (HostImpl.none (σ := PUnit)) PUnit.unit ht hlen,
        mem_ir_iffG hg' (HostImpl.none (σ := PUnit)) PUnit.unit ht' hlen', h.obs calls ht]
    · have ht' := typedCalls_castG h.ty ht
      have hlen' : (LinkedG.castCalls h.len calls).length = outs.length := by
        rw [length_castCallsG]
        exact hlen
      have hvs' : ValTy.checkList g'.imp.exports[Fin.cast h.len j].ty.params vs = true := by
        rw [h.ty]
        exact hvs
      have e₁ := quiet_iffG (prof := prof) hg (HostImpl.none (σ := PUnit)) PUnit.unit calls outs
        j vs ht hvs
      have e₂ := quiet_iffG (prof := prof) hg' (HostImpl.none (σ := PUnit)) PUnit.unit
        (LinkedG.castCalls h.len calls) outs (Fin.cast h.len j) vs ht' hvs'
      have e₃ := h.quiet calls outs j vs ht hvs (HostImpl.none (σ := PUnit)) PUnit.unit
      exact ⟨fun hd => (e₂.1 (e₃.1 (e₁.2 ⟨hlen, hd⟩))).2,
        fun hd => (e₁.1 (e₃.2 (e₂.2 ⟨hlen', hd⟩))).2⟩
    · rw [inf_iff_profileG (prof := prof) hg a out ht (HostImpl.none (σ := PUnit)) PUnit.unit,
        inf_iff_profileG (prof := prof) hg' _ out (typed_castStreamG h.ty ht)
          (HostImpl.none (σ := PUnit)) PUnit.unit]
      exact h.prod a out ht _ _
  · rintro ⟨hty, ⟨len₁, hfin⟩, ⟨len₂, hdiv⟩, ⟨len₃, hinf⟩⟩
    obtain ⟨len, hty⟩ := sameTypes_iffG.1 hty
    refine ⟨len, hty, fun calls ht σ impl h₀ => ?_,
      fun calls outs j vs ht hvs σ impl h₀ => ?_, fun a out ht σ impl h₀ => ?_⟩
    · have ht' := typedCalls_castG hty ht
      rw [sessObs_eq_irG hg impl h₀ calls ht, sessObs_eq_irG hg' impl h₀ _ ht']
      ext x
      constructor
      · rintro ⟨outs, rfl, hlen, hm⟩
        exact ⟨outs, rfl, by rw [length_castCallsG]; exact hlen, (hfin calls outs ht hlen).1 hm⟩
      · rintro ⟨outs, rfl, hlen', hm⟩
        have hlen : calls.length = outs.length := by
          rw [← length_castCallsG len calls]
          exact hlen'
        exact ⟨outs, rfl, hlen, (hfin calls outs ht hlen).2 hm⟩
    · have ht' := typedCalls_castG hty ht
      have hvs' : ValTy.checkList g'.imp.exports[Fin.cast len j].ty.params vs = true := by
        rw [hty]
        exact hvs
      rw [quiet_iffG hg impl h₀ calls outs j vs ht hvs,
        quiet_iffG hg' impl h₀ _ outs _ vs ht' hvs', length_castCallsG]
      constructor
      · rintro ⟨hlen, hd⟩
        exact ⟨hlen, (hdiv calls outs j vs ht hlen hvs).1 hd⟩
      · rintro ⟨hlen, hd⟩
        exact ⟨hlen, (hdiv calls outs j vs ht hlen hvs).2 hd⟩
    · rw [← inf_iff_profileG hg a out ht impl h₀,
        ← inf_iff_profileG hg' _ out (typed_castStreamG hty ht) impl h₀]
      exact hinf a out ht

end Linked

/-! ## Chains -/

/-- **One more importer on a chain with a simple base meets `ProfOk`.** -/
theorem extOk_profOk (o : GrowOracle) {n : LinkedN} {Ib : SInst} {Is : List SInst}
    {b : SimpleI} {w : List Nat} (h : n.ExtOk Ib Is b w) :
    (LinkedG.mk (n.spec Ib Is) b w).ProfOk o where
  adeq := LinkedN.adeq _ h.good h.isInst h.chain.chainOk
  adeqD := LinkedN.adeqD_profile o h.good h.isInst h.chain.chainOk
  adeqI := chainExp_adeqI _ (Simple.expSpec_adeq _ h.good h.isInst)
    (Simple.expSpec_adeqI _ h.good h.isInst) h.chain.chainOk
  det := chainExp_det o (Simple.expSpec_det o _ _)
  ref := chainExp_refAdeqUXD _ (Simple.expSpec_refAdeqUXD _ h.good h.inst h.isInst h.split
    h.names) h.chain
  link := h.link

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf
