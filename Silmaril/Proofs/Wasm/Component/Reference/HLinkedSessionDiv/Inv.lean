module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Classify
public import Silmaril.Wasm.Component.Reference.HostWrite.Thms

/-!
# Diverging sessions of `HLinked2.toRef`: reference to specification

* `linkDivH_inv`: from a configuration between calls (`ReadyL` at `l.toW`) whose programs are
  host-safe for the logging host (`CfgSafe logExt`), a top-level call diverging quietly in host
  state `st` is a specification round that never answers after its host calls end in `st`
  (`HLinked2.RoundDiv`): the invocation and the deterministic prefix (`call_atLKTS`), then
  `ldiv_classifyH` along the explicit run of the divergence (`callQuiet_irun`), with the log
  length as measure: the logging host appends one event per answered host call, and along the
  run the host state is unchanged or its log strictly grows (`HostWrite`);
* `hlinked2_divRefToSpec`: `HLinked2.DivRefToSpec` under `HLinked2.Adequate` and a typed host,
  from the instantiation of `l.toRef`, the inversion of the session prefix (`sessH_inv`) and the
  host-safety of the configuration reached (`HLinked2.logSession_cfgSafe`);
* `hlinked2_sessDivs_eq_refDivs`: with `hlinked2_divSpecToRef`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Proofs.Wasm.Component.Reference.HostWrite
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "RVal" => Silmaril.Wasm.Component.Reference.Val
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {prof : ProfileKind} {σ₀ : Type}
  {g : σ₀ → HostFuncId → List RVal → Option (List RVal × σ₀)}

/-- The dispatcher of the logging host is host-safe for `logExt`. -/
theorem dispatchSafe_log :
    DispatchSafe logExt (DI P (answerImplS (HLinked2.logG g))) :=
  hostSafe_dispatch (hostImplSafe_answerLog g) _ _ _

section Call

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) (σ₀ × List HLinked2.HostEvent)}
  {fs : List (CFuncInst (core3P P))}

/-- **A quietly diverging call of the reference machine between calls is a specification round
that never answers**, its host calls answered by the logging host from the host state of the call
to the host state of the divergence. -/
theorem linkDivH_inv (hT : l.HostTyped g)
    (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOkH l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P (σ₀ × List HLinked2.HostEvent)} {ST : List Subtask}
    {h₀ : σ₀ × List HLinked2.HostEvent} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k)
    (hsafe : CfgSafe logExt (readyCfgL cs ιe ιi fs G ST h₀)) (j : Fin l.imp.exports.length)
    {vs : List IVal} (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {st : σ₀ × List HLinked2.HostEvent}
    (hd : CallQuietDiverges prof (fun _ _ => false) (DI P (answerImplS (HLinked2.logG g)))
      (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩ ⟨l.host.length + l.exp.exports.length + j⟩
      (vs.map toRefVal) st) :
    HLinked2.RoundDiv P l Ie Ii (HLinked2.logG g) u π h₀ j vs st := by
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
  have hfj : fs[l.host.length + l.exp.exports.length + j]? = some (.lifted
      (s₀.funcs.length + Ii.addr f.1) (liftedFt l.imp.exports[j]) {} ⟨2⟩) := ha ▸ hfs j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS
    (impl := answerImplS (HLinked2.logG g)) prof cs ιe ιi fs G ST h₀ k
    (l.host.length + l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf
    R.thI R.leave hfj
  have S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hF := gframe_of hat
  have hI₀ : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) (u, Ii.initThread f) π :=
    linv_ready R.inv hf₂ rfl
  have hck : checkLower l.imp.exports[j].ty.params vs =
      some (lowerArgs l.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  obtain ⟨m₁, t, s, ht0, ht, hio⟩ := callQuiet_irun hd
  have e₁ := invoke_invL s
  subst e₁
  have hstart : M₀ = coreCfg (extG M₀ ιe [] [] [] [] M₀.conts h₀) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) := by
    have e := hat.start
    rw [extN_eq_extG] at e
    rw [← hat.host]
    exact e
  have hp₀ := ht.lrun hpre ht0
  rw [hstart] at hp₀
  -- host-safety along the run
  have hsafe₀ : CfgSafe logExt (t 0) := by
    rw [ht0]
    exact step_cfgSafe dispatchSafe_log s hsafe fun p e => by cases e
  have hmono : ∀ a b, a ≤ b → (t b).host = (t a).host ∨
      (t a).host.2.length < (t b).host.2.length := by
    intro a b hab
    obtain ⟨tra, ra, hha⟩ := ht.steps_le (Nat.zero_le a)
    have hsa := (steps_cfgSafe dispatchSafe_log ra hsafe₀ fun p hp => absurd hp (hha _)).1
    obtain ⟨trb, rb, hhb⟩ := ht.steps_le hab
    rcases hostChain_logExt (steps_cfgSafe dispatchSafe_log rb hsa
      fun p hp => absurd hp (hhb _)).2 with e | ⟨-, hl⟩
    · exact .inl e
    · exact .inr hl
  have hgμ : ∀ s fn args rs s', HLinked2.logG g s fn args = some (rs, s') →
      s.2.length < s'.2.length := by
    intro s fn args rs s' h
    simp only [HLinked2.logG, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨rs', t'⟩, -, rfl, rfl⟩ := h
    simp
  have hH := handlesB_answer (prof := prof) (P := P) (g := HLinked2.logG g) S₀.arity S₀.floats
    S₀.wireTy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hat S.hostFn
  obtain ⟨rs, dss, xz, π₁, hpath, hrel, hexp, hhr, hsrc⟩ := ldiv_classifyH (u₀ := u₀) S hF hH
    (HostTyped.logG hT) (exitsQuietH_call (u₀ := u₀) S hat hft') ht (fun s => s.2.length) hgμ
    hmono hio (z₀ := ⟨0 + tr₁.length, _, (u, Ii.initThread f), π, ιe, [], [], [], [], M₀.conts,
      h₀⟩) ⟨hp₀, R.thE, hI₀⟩
  exact ⟨⟨j, vs, f, rs, dss⟩, xz.1, xz.2, π₁, rfl, rfl, ⟨_, hck, hf₁, hf₂, hrel⟩,
    .cons (.call u f) hpath, hexp, hhr, hsrc⟩

end Call

/-! ## Assembly -/

/-- **Reference divergence of a linked session with host imports is specification divergence,
with the host log**: under `HLinked2.Adequate` and a typed host, `HLinked2.DivRefToSpec` holds at
every profile and component choice profile. -/
theorem hlinked2_divRefToSpec (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) : HLinked2.DivRefToSpec P prof l g := by
  intro s₀ calls j vs ht hvs p hp
  obtain ⟨m₀, inst, es, fs', m₁, f, hr, hfs', hf, hSq, hd⟩ := hp
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
  have hround := linkDivH_inv (prof := prof) hT S₀ rfl hfs R' hsafe₁ j hvs hd
  obtain rfl := SessionAdequacy.refOuts_inj ho'
  exact ⟨Ie, Ii, hs, u', π', m₁.host, hFe.isInst, hIi, hspec, hhr, hround⟩

/-- **The diverging session calls of a linked component with host imports, with the host log**:
those of the specification are those of the reference machine. -/
theorem hlinked2_sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    HLinked2.sessDivs P l g s₀ calls j vs = HLinked2.refDivs P prof l g s₀ calls j vs :=
  Set.Subset.antisymm (hlinked2_divSpecToRef P prof hl g hT s₀ calls j vs)
    (hlinked2_divRefToSpec P prof hl g hT s₀ calls j vs ht hvs)

/-! ## The equivalence with quiet divergence -/

theorem hostTyped_congr {l l' : HLinked2} (h : l'.host = l.host) {σ : Type}
    {g : σ → HostFuncId → List RVal → Option (List RVal × σ)} (hT : l.HostTyped g) :
    l'.HostTyped g := by
  intro s i hi ws rs s' hg
  have hi' : i < l.host.length := h ▸ hi
  obtain ⟨us, e, hc⟩ := hT s i hi' ws rs s' hg
  refine ⟨us, e, ?_⟩
  rw [List.getElem_of_eq h hi]
  exact hc

theorem typedCalls_castH {l l' : HLinked2} (h : HLinked2.RefSessEquivH P prof l l')
    {calls : List (Fin l.imp.exports.length × List IVal)} (ht : SimpleI.TypedCalls l.imp calls) :
    SimpleI.TypedCalls l'.imp (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len calls) := by
  intro q hq
  obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
  show ValTy.checkList l'.imp.exports[Fin.cast h.len q₀.1].ty.params q₀.2 = true
  rw [h.ty]
  exact ht q₀ hq₀

/-- **`RefSessEquivD` with the divergence clause on the specification**: for adequate linked
components with host imports, the reference-defined equivalence with quiet divergence and the
host log is `RefSessEquivH` together with the same specification divergences under every typed
host. -/
theorem hlinked2_refSessEquivD_iff {l l' : HLinked2} (hl : l.Adequate) (hl' : l'.Adequate) :
    HLinked2.RefSessEquivD P prof l l' ↔ ∃ h : HLinked2.RefSessEquivH P prof l l',
      ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
        (vs : List IVal), SimpleI.TypedCalls l.imp calls →
        ValTy.checkList l.imp.exports[j].ty.params vs = true →
        ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
          ∀ s₀ : σ, HLinked2.sessDivs P l g s₀ calls j vs =
            HLinked2.sessDivs P l' g s₀
              (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len calls)
              (Fin.cast h.len j) vs := by
  have key : ∀ (h : HLinked2.RefSessEquivH P prof l l')
      (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
      (vs : List IVal), SimpleI.TypedCalls l.imp calls →
      ValTy.checkList l.imp.exports[j].ty.params vs = true →
      ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
        ∀ s₀ : σ,
        (HLinked2.sessDivs P l g s₀ calls j vs =
            HLinked2.sessDivs P l' g s₀ (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len
              calls) (Fin.cast h.len j) vs ↔
          HLinked2.refDivs P prof l g s₀ calls j vs =
            HLinked2.refDivs P prof l' g s₀ (Linked2.castCalls (l := l.toL2) (l' := l'.toL2)
              h.len calls) (Fin.cast h.len j) vs) := by
    intro h calls j vs ht hvs σ g hT s₀
    have hvs' : ValTy.checkList l'.imp.exports[Fin.cast h.len j].ty.params vs = true := by
      rw [h.ty j]
      exact hvs
    rw [hlinked2_sessDivs_eq_refDivs P prof hl g hT s₀ calls j vs ht hvs,
      hlinked2_sessDivs_eq_refDivs P prof hl' g (hostTyped_congr h.host hT) s₀ _ _ vs
        (typedCalls_castH h ht) hvs']
  constructor
  · intro h
    exact ⟨h.toRefSessEquivH, fun calls j vs ht hvs σ g hT s₀ =>
      (key h.toRefSessEquivH calls j vs ht hvs g hT s₀).mpr (h.div calls j vs ht hvs g hT s₀)⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, fun calls j vs ht hvs σ g hT s₀ =>
      (key h calls j vs ht hvs g hT s₀).mp (hd calls j vs ht hvs g hT s₀)⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
