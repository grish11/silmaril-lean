module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.Round
public import Silmaril.Wasm.Component.Reference.LinkedSessionDivInv.Defs

/-!
# Diverging linked sessions: reference to specification

* `exitsQuiet_call`: in the frame of a linked call (`CallAtLK`), an exit of the importer's core
  phase other than a callout does not diverge: returned values of the result types (typed by
  the importer's specification, `results_typed`) resolve the call or trap in the lift, and a
  Core trap locks down;
* `linkDiv_inv`: from a configuration between linked calls (`ReadyL`), a diverging top-level
  call is a round that never answers (`Linked2.RoundDiv`): the host's invocation and the
  deterministic prefix (`call_atLK`), then `ldiv_classify` from the importer's core activation;
* `sessDivL_inv`: a resumable session of the reference machine ending in a diverging call
  (`SessDiv`) is a specification session (`linkCallK`, `linkCallT`, as `sessL_inv`) followed by
  a round that never answers;
* `linked2_divRefToSpec`: `Linked2.DivRefToSpec` under `Linked2.Adequate`, from the
  instantiation of `l.toRef` (as `linked2_sess_refToSpec`);
* `linked2_sessDivs_eq_refDivs`, `linked2_refSessEquivD_iff`: with #730's
  `linked2_divSpecToRef`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {Op₀ Oc₀ : Own}

/-! ## The exits of a linked call -/

/-- **In the frame of a linked call, the exits of the importer's core phase other than callouts
do not diverge.** -/
theorem exitsQuiet_call {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k j a : Nat}
    {x : SimpleExport} {vs : List Silmaril.Wasm.Component.Val} {M₀ : Machine.Config (E3 P) σ}
    {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    (S : LStat P l Ie Ii u₀ F₀ M₀ Op₀)
    (hat : CallAtLK prof P impl cs ιe ιi fs G ST h₀ k j x a vs M₀ th K segs rest)
    {f : Ii.F.Op} (hft : Ii.exports.get f.1 = fnOf x.ty.flat) :
    ExitsQuiet prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f M₀ th K segs rest := by
  intro ιe' N C y xp π lb m₁ hI hnco hx
  rcases hx with ⟨zs, hst, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨h, ys, hc⟩
  · obtain ⟨cvs, hcode, hm⟩ := status_values hst
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
    obtain ⟨ts, hs, ht⟩ := hI.typed S
    have hc : (y.2.config (Store.mapH (gL P l) y.1)).code =
        Silmaril.Wasm.Execution.Core.vals cvs :=
      (config_code_mapH (gL P l) y.1 y.2).trans hcode
    obtain ⟨vs', hv, hvm⟩ := values_back P hL hs ht hc
    have hm' : (vs'.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
        some zs := by
      rw [hvm]
      exact hm
    have hvs' : vs' = cvs := (map_val_of_mapM _ hm').symm.trans hvm
    have hr : Silmaril.Wasm.Game.ResultAt xp.1 xp.2 (.values cvs) := hvs' ▸ hv
    obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
      (valEnv_throwsBelow Ii _) hI.run hr
    have hty : zs.map (·.type) = ValTy.flatList x.ty.results := results_typed hft hw hm
    cases hl : liftArgs x.ty.results zs with
    | some ws =>
      obtain ⟨C', hRes⟩ := hat.ret ιe' N C y zs ws hty hl
      exact ResolvesAtL.not_diverges hRes
    | none => exact TrapsFrom.not_diverges (hat.trap ιe' N C y zs hty hl).trapsFrom
  · exact not_diverges_trapCfg _
  · exact absurd hc (hnco h ys)

/-! ## One call -/

variable {B₀ : Machine.Config (E3 P) σ} {fs : List (CFuncInst (core3P P))}

/-- **A diverging call of the reference machine between linked calls is a specification round
that never answers.** -/
theorem linkDiv_inv (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (j : Fin l.imp.exports.length)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (hd : CallDiverges prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩
      ⟨l.exp.exports.length + j⟩ (vs.map toRefVal)) :
    Linked2.RoundDiv P l Ie Ii u π j vs := by
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := S₀.impGood.core _ hx
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : l.imp.mod.exports[l.imp.exports[j].core] = (nm, l.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs l.imp.exports[j].ty.params vs).map (·.type) =
      l.imp.mod.exports[l.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI S₀.impInst hk hxs
  have hft' : Ii.exports.get f.1 = fnOf l.imp.exports[j].ty.flat := by rw [hft, hflat]
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[j].core 0 = Ii.addr f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.exp.exports.length + j]? = some (.lifted (s₀.funcs.length + Ii.addr f.1)
      (liftedFt l.imp.exports[j]) {} ⟨2⟩) := ha ▸ hfs j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLK (impl := impl) prof cs ιe ιi fs G
    ST h₀ k (l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf R.thI
    R.leave hfj
  have S : LStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hI₀ : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) (u, Ii.initThread f) π :=
    linv_ready R.inv hf₂ rfl
  have hck : checkLower l.imp.exports[j].ty.params vs =
      some (lowerArgs l.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  obtain ⟨m₂, st, d⟩ := hd
  rw [invoke_invL st] at d
  have d₀ := hpre.diverges d
  rw [hat.start] at d₀
  obtain ⟨rs, dss, xz, π₁, hpath, hrel, hexp, hsrc⟩ := ldiv_classify S hat.frame
    (exitsQuiet_call (s₀ := s₀) (Oc₀ := shOwn (sh s₀) (ownOf u₀)) S hat hft')
    (z₀ := ⟨_, (u, Ii.initThread f), π, ιe, [], M₀.conts⟩) ⟨d₀, R.thE, hI₀⟩
  exact ⟨⟨j, vs, f, rs, dss⟩, xz.1, xz.2, π₁, rfl, rfl, ⟨_, hck, hf₁, hf₂, hrel⟩,
    .cons (.call u f) hpath, hexp, hsrc⟩

/-! ## Sessions -/

/-- **Reference sessions ending in a diverging call are specification sessions ending in a round
that never answers**, between linked calls. -/
theorem sessDivL_inv (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) (j : Fin l.imp.exports.length)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    ∀ (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
      (ST : List Subtask) (h₀ : σ) (u π : Store Nat) (k : Nat)
      (outs : List (Option (List Silmaril.Wasm.Component.Reference.Val))),
      ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k → SimpleI.TypedCalls l.imp calls →
      SessDiv prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k (callArgsL l calls) outs
        ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) →
      ∃ (outs' : List (Option (List Silmaril.Wasm.Component.Val))) (u' π' : Store Nat),
        Linked2.SessSpec P l Ie Ii u π calls outs' u' π' ∧ outs = refOuts outs' ∧
        Linked2.RoundDiv P l Ie Ii u' π' j vs
  | [], cs, ιe, ιi, G, ST, h₀, u, π, k, outs, R, _, hS => by
    cases hS with
    | div hd => exact ⟨[], u, π, .nil u π, rfl, linkDiv_inv S₀ hB₀ hfs R j hvs hd⟩
  | (j', vs') :: calls, cs, ιe, ιi, G, ST, h₀, u, π, k, outs, R, ht, hS => by
    have hvs' : ValTy.checkList l.imp.exports[j'].ty.params vs' = true := ht _ List.mem_cons_self
    have ht' : SimpleI.TypedCalls l.imp calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    cases hS with
    | ret hcall hS' =>
      obtain ⟨r, uc, q, hu, -, hpath, hobs, hnext⟩ := linkCallK S₀ hB₀ hfs R j' hvs' hcall
      obtain ⟨ws, rfl, hua⟩ : ∃ ws : List Silmaril.Wasm.Component.Val,
          _ = ws.map toRefVal ∧ uc.a = some (.vals ws) := hobs
      obtain ⟨cs₁, ιe₁, ιi₁, G₁, ST₁, u₁, π₁, rfl, hexp₁, rfl, R₁⟩ := hnext _ rfl
      obtain ⟨outs', u', π', hspec, rfl, hd⟩ :=
        sessDivL_inv S₀ hB₀ hfs j hvs calls cs₁ ιe₁ ιi₁ G₁ ST₁ h₀ u₁ π₁ (k + 1) _ R₁ ht' hS'
      obtain ⟨xs, dss, hcl, hq₁, hq₂, hrel, rfl⟩ := hu
      exact ⟨some ws :: outs', u', π',
        .round ⟨j', vs', r.q, r.cs, r.a, dss⟩ ⟨xs, hcl, hq₁, hq₂, hrel⟩ hpath (expSeg_toT hexp₁)
          hua hspec, rfl, hd⟩
    | trap hcall hS' =>
      obtain ⟨d, u₁, π₁, rfl, rfl, hok, hans, hpath, hexp, hR⟩ :=
        linkCallT S₀ hB₀ hfs R j' hvs' hcall
      have R₁ : ReadyL P l Ie Ii s₀ u₀ F₀ _ ιe ιi G u₁ π₁ (k + 1) :=
        ⟨hR, R.thE, R.thI, R.leave, fresh_succL R.fresh⟩
      rw [resumeCfg_readyL] at hS'
      obtain ⟨outs', u', π', hspec, rfl, hd⟩ :=
        sessDivL_inv S₀ hB₀ hfs j hvs calls _ ιe ιi G ST _ u₁ π₁ (k + 1) _ R₁ ht' hS'
      exact ⟨none :: outs', u', π', .round d hok hpath hexp hans hspec, rfl, hd⟩

/-! ## Assembly -/

/-- **Reference divergence of a linked session is specification divergence**: under
`Linked2.Adequate`, `Linked2.DivRefToSpec` holds at every profile and component choice
profile. -/
theorem linked2_divRefToSpec (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) : Linked2.DivRefToSpec P prof l := by
  intro calls j vs ht hvs σ impl h₀ outs hout
  obtain ⟨hEg, hEi, hIg, hIi, har, hff, hW, hN, hn, hS⟩ := hl
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursL_inst (Pf := P) (σ := σ) hEg hEi hIg hIi har
    ⟨hS.imp.data, hS.imp.elems⟩ hW hN
  obtain ⟨Ii, hI⟩ := hIi.inst
  obtain ⟨r, hrs, hh, hres⟩ := hall Ii hI
  obtain ⟨m₀, inst, es, fs, f, hr, hfs, hf, hSq⟩ := hout
  have he : m₀ = afterLink P (reloc cse (Store.mapH Prod.fst r))
      (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀ ∧
      inst = ⟨0⟩ ∧ es = exportMapL l := by
    simpa only [InstResult.instance.injEq] using hres prof (linkHost impl) h₀ _ hr
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hfs' : fs = calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (mapM_lookupL hIg calls))
  have hf' : f = ⟨l.exp.exports.length + j⟩ :=
    Option.some.inj (hf.symm.trans (exportMapL_lookup hIg j))
  subst hfs' hf'
  have hz : (calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId)).zip
      (calls.map fun q => q.2.map toRefVal) = callArgsL l calls := by
    rw [← zip_callArgsL calls, List.map_map]
    rfl
  rw [hz] at hSq
  have S₀ : LStat P l Ie Ii Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (readyCfgL (σ := σ) (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      (ownOf Ie.store) :=
    lstat_init hEg hIg hW hn har hff hFe hI hh _ rfl
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hI.1.choose_spec
  have R₀ : ReadyL P l Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
      (Garb.empty : Garb P σ) Ii.store Ie.store 0 :=
    { inv := lready_init hg₀ hgu (linkStore_mapH hn hW hFe hrs hh) rfl
        hFe.isInst.1.choose_spec.ok hI.1.choose_spec.ok
      thE := threadsOk_empty
      thI := threadsOk_empty
      leave := rfl
      fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) } }
  have hok : LiftedOk l Ii Ie.store (liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩
      l.exp.exports ++ liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) :=
    liftedOk_afterLink hI hIg hFe
  obtain ⟨outs', u', π', hspec, he', hd⟩ :=
    sessDivL_inv S₀ rfl hok j hvs calls _ _ _ _ _ h₀ _ _ 0 _ R₀ ht hSq
  obtain rfl := SessionAdequacy.refOuts_inj he'
  exact ⟨Ie, Ii, u', π', hFe.isInst, hI, hspec, hd⟩

/-- **The diverging session calls of the specification are those of the reference machine.** -/
theorem linked2_sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) :
    Linked2.sessDivs P l calls j vs = Linked2.refDivs P prof l impl h₀ calls j vs :=
  Set.Subset.antisymm
    (LinkedSessionDiv.linked2_divSpecToRef P prof l hl calls j vs ht hvs impl h₀)
    (linked2_divRefToSpec P prof l hl calls j vs ht hvs impl h₀)

/-- Typed calls stay typed under `castCalls`, for the same export types. -/
theorem typedCalls_cast {l l' : Linked2} (h : Linked2.RefSessEquiv P prof l l')
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    (ht : SimpleI.TypedCalls l.imp calls) :
    SimpleI.TypedCalls l'.imp (Linked2.castCalls h.len calls) := by
  intro q hq
  obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
  show ValTy.checkList l'.imp.exports[Fin.cast h.len q₀.1].ty.params q₀.2 = true
  rw [h.ty]
  exact ht q₀ hq₀

/-- **`RefSessEquivD` with the divergence clause on the specification.** -/
theorem linked2_refSessEquivD_iff {l l' : Linked2} (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquivD P prof l l' ↔ ∃ h : Linked2.RefSessEquiv P prof l l',
      ∀ (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
        (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val),
        SimpleI.TypedCalls l.imp calls → ValTy.checkList l.imp.exports[j].ty.params vs = true →
        Linked2.sessDivs P l calls j vs =
          Linked2.sessDivs P l' (Linked2.castCalls h.len calls) (Fin.cast h.len j) vs := by
  have key : ∀ (h : Linked2.RefSessEquiv P prof l l')
      (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val),
      SimpleI.TypedCalls l.imp calls → ValTy.checkList l.imp.exports[j].ty.params vs = true →
      ∀ {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ),
        (Linked2.sessDivs P l calls j vs =
            Linked2.sessDivs P l' (Linked2.castCalls h.len calls) (Fin.cast h.len j) vs ↔
          Linked2.refDivs P prof l impl h₀ calls j vs =
            Linked2.refDivs P prof l' impl h₀ (Linked2.castCalls h.len calls) (Fin.cast h.len j)
              vs) := by
    intro h calls j vs ht hvs σ impl h₀
    have hvs' : ValTy.checkList l'.imp.exports[Fin.cast h.len j].ty.params vs = true := by
      rw [h.ty j]
      exact hvs
    rw [linked2_sessDivs_eq_refDivs P prof l hl calls j vs ht hvs impl h₀,
      linked2_sessDivs_eq_refDivs P prof l' hl' _ _ vs (typedCalls_cast h ht) hvs' impl h₀]
  constructor
  · intro h
    exact ⟨h.toRefSessEquiv, fun calls j vs ht hvs =>
      (key h.toRefSessEquiv calls j vs ht hvs (σ := Unit) HostImpl.none ()).mpr
        (h.div calls j vs ht hvs HostImpl.none ())⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, fun calls j vs ht hvs σ impl h₀ =>
      (key h calls j vs ht hvs impl h₀).mp (hd calls j vs ht hvs)⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
