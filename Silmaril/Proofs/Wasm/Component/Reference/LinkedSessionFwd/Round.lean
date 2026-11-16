module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Machine

/-!
# Forward runs of a linked call: a specification round as a segmented run

A round of the importer's instance (its path from `.running f s t` along `callMoves rs` and the
answer `w`), whose core import calls are related by `ImpRel` to component import calls answered
by the exporter's specification (`ExpRunT`, traps continuing), is followed by the shared thread:

* `LInv.callout_fwd`: a callout of the importer's part is a callout of the shared thread to the
  trampoline of the import, on the same flat arguments;
* `path_round_inv`, `path_ret_inv`, `path_doomed`: inversions of the instance's path; after an
  import call answered by a trap the round ends at once in a trap, in the store of the callout;
* `rounds_fwd`: from `LInv`, the round is a segmented run `LSeg` of the shared thread followed
  by a `RoundEnd`: either the importer's part finished with the round's answer (`LInv` at the
  exporter's end store), or a nested call trapped (`NestTrap`: the exporter's run trapped, its
  results did not lift, or the callout's arguments did not lift), the round answering a trap
  and `LReady` holding at the core store of the trap, the importer's store at the callout and the
  exporter's store after the trapped call.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4 Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type}

/-! ## Callouts -/

/-- A Core status is a callout at a host-call redex. -/
theorem statusP_of_decomp {H : Type} {s : Store H} {t : STh} {E : Silmaril.Wasm.SingleThreaded.Ctx}
    {a : Nat} {c : H} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hd : Silmaril.Wasm.SingleThreaded.decompose? s (t.config s).code = some (E, a, c, args)) :
    Silmaril.Wasm.Game.statusP P s t = .callout c args := by
  have n₁ : ¬ ∃ vs, (t.config s).code = Silmaril.Wasm.Execution.Core.vals vs := by
    rintro ⟨vs, hv⟩
    rw [hv, Silmaril.Wasm.SingleThreaded.decompose?_vals_nil] at hd
    cases hd
  have n₂ : ¬ (t.config s).code = [.trap] := fun hv => by
    rw [hv, decompose?_trap] at hd
    cases hd
  have n₃ : ¬ ∃ b, (t.config s).code = Silmaril.Wasm.Execution.Core.throwing b := by
    rintro ⟨b, hv⟩
    rw [hv, decompose?_throwing'] at hd
    cases hd
  unfold Silmaril.Wasm.Game.statusP
  dsimp only
  split_ifs
  all_goals rw [hd]

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op}

/-- **A callout of the importer's part is a callout of the shared thread** to the trampoline of
the import `k` (type `p`, wired to the exporter's export `xe` of type `p`), on the flat arguments
of the part's. -/
theorem LInv.callout_fwd (S : LStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {k : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args) {e : Ii.E.Op}
    (he : Ii.importOp? k args = some e) :
    ∃ (nm : String) (p : FuncTy) (w : Nat) (xe : SimpleExport) (ys : List Flat)
      (E : Silmaril.Wasm.SingleThreaded.Ctx) (a : Nat),
      l.imp.imports[k]? = some (nm, p) ∧ l.wire[k]? = some w ∧ l.exp.exports[w]? = some xe ∧
      xe.ty = p ∧
      Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args) ∧
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys ∧
      (E3 P).status y.1 y.2 = .callout (.lowered (l.wireFid k) (witFt p) {} ⟨2⟩) ys ∧
      ys.map (·.type) = ValTy.flatList p.params := by
  obtain ⟨E, a, hdx⟩ := hc
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
  have hdy := (decompose?_config_mapH (gL P l) y.1 y.2).symm.trans (link_callout hL hdx)
  obtain ⟨⟨E', A, h, args'⟩, hd, hq⟩ := Option.map_eq_some_iff.mp hdy
  simp only [mapR, Prod.mk.injEq] at hq
  obtain ⟨-, -, hgh, hargs⟩ := hq
  obtain ⟨fi, -, -, -, hf, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hI.funcs] at hf
  obtain ⟨k', nm, p, rfl, hk⟩ := S.tramp A fi _ hf hcode
  have hk' : k' < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
  have hkl : k' < l.wire.length := S.wireTy.length ▸ hk'
  have hkk : k' = k := by
    rw [← hgh]
    exact (trampIdxL_wireFid S.nodup hkl _ _ _).symm
  subst hkk
  have hek := ifaceOp?_some he
  have h2 : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get e.1).params args :=
    hek.2 ▸ e.2.2
  rw [imports_get S.impGood S.impInst e k' hk' hek.1, (List.getElem?_eq_some_iff.mp hk).2] at h2
  obtain ⟨ys, hys⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome h2
  have hargs' : args' = args := by
    rw [hargs]
    exact map_val_of_flat _ hys
  subst hargs'
  obtain ⟨w, hw⟩ : ∃ w, l.wire[k']? = some w := ⟨_, List.getElem?_eq_getElem hkl⟩
  obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty k' w hw
  have hpx : xe.ty = p := by
    rw [hk] at hty
    simp only [Option.map_some, Option.some.injEq] at hty
    exact hty.symm
  refine ⟨nm, p, w, xe, ys, E, a, hk, hw, hxe, hpx, hdx, hys, ?_, flat_types_of_hasVal h2 hys⟩
  show flatStatus (Silmaril.Wasm.Game.statusP P y.1 y.2) = _
  rw [statusP_of_decomp hd]
  simp only [flatStatus, hys]

/-! ## Inverting the instance's path -/

theorem path_round_inv {s : Store Nat} {t : STh} {e : Ii.E.Op} {v : Ii.E.Ar e}
    {rest : List (Move Ii.E Ii.F)} {q : Ii.HState}
    (h : Ii.Path P (.running f s t) (.inl (.ask e) :: .inl (.ans e v) :: rest) q) :
    ∃ (s' : Store Nat) (t' : STh) (k : Nat) (args : List Silmaril.Wasm.Execution.Core.Val),
      Silmaril.Wasm.Game.Reach P (s, t) (s', t') ∧ Silmaril.Wasm.Game.CalloutAt s' t' k args ∧
      Ii.importOp? k args = some e ∧
      Ii.Path P (.running f s' (Silmaril.Wasm.SingleThreaded.resumeResult s' t'
        (Silmaril.Wasm.Game.Answer.toResult v))) rest q := by
  cases h with
  | cons h₁ h₂ =>
    cases h₁ with
    | ucall run co op =>
      cases h₂ with
      | cons h₃ h₄ =>
        cases h₃ with
        | uret _ => exact ⟨_, _, _, _, run, co, op, h₄⟩

theorem path_ret_inv {s : Store Nat} {t : STh} {w : Ii.F.Ar f} {q : Ii.HState}
    (h : Ii.Path P (.running f s t) [.inr (.ans f w)] q) :
    ∃ (s' : Store Nat) (t' : STh) (r : Silmaril.Wasm.Execution.Core.Result),
      Silmaril.Wasm.Game.Reach P (s, t) (s', t') ∧ Silmaril.Wasm.Game.ResultAt s' t' r ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w ∧ q = .idle s' := by
  cases h with
  | cons h₁ h₂ =>
    cases h₁ with
    | oret run final answer =>
      cases h₂
      exact ⟨_, _, _, run, final, answer, rfl⟩

/-- **After an import call answered by a trap the round ends in a trap** at the store of the
callout: no further import call, the answer a trap. -/
theorem path_doomed {s : Store Nat} {t : STh} {k : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hc : Silmaril.Wasm.Game.CalloutAt s t k args)
    {rs : List (Σ e : Ii.E.Op, Ii.E.Ar e)} {w : Ii.F.Ar f} {u₁ : Store Nat}
    (h : Ii.Path P (.running f s (Silmaril.Wasm.SingleThreaded.resumeResult s t
      .trap)) (callMoves rs ++ [.inr (.ans f w)]) (.idle u₁)) :
    rs = [] ∧ u₁ = s ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) .trap = some w := by
  obtain ⟨E, a, hd⟩ := hc
  have hd' : Silmaril.Wasm.SingleThreaded.decompose? (t.config s).store (t.config s).code =
      some (E, a, k, args) := (Silmaril.Wasm.SingleThreaded.Thread.config_store s t).symm ▸ hd
  have hcfg : (Silmaril.Wasm.SingleThreaded.resumeResult s t .trap).config s =
      ⟨s, (t.config s).frame, E.fill [.trap]⟩ := by
    rw [resumeResult_config hd' .trap, Silmaril.Wasm.SingleThreaded.Thread.config_store]
    rfl
  cases rs with
  | cons r rs =>
    obtain ⟨e, v⟩ := r
    obtain ⟨s', t', k', args', run, co, -, -⟩ := path_round_inv (Ii := Ii) (P := P) (f := f)
      (rest := callMoves rs ++ [.inr (.ans f w)]) (v := v) (by simpa [callMoves] using h)
    exact (reach_doomed_callout run hcfg co).elim
  | nil =>
    obtain ⟨s', t', r, run, final, hw, hq⟩ := path_ret_inv (by simpa [callMoves] using h)
    obtain ⟨hr, hs⟩ := Silmaril.Proofs.Wasm.Game.Linking.Split.reach_doomed' run hcfg final
    cases hq
    subst hr
    exact ⟨rfl, hs, hw⟩

/-! ## Rounds -/

/-- **A nested call that traps the machine** at the callout `yc` of the shared thread, the trap
holding the core store `c`: the callout's arguments do not lift (`c` is the callout's store), or
the exporter's run traps or returns results that do not lift (`c` is the store of its end). -/
def NestTrap (B : Machine.Config (E3 P) σ) (yc : CoreSt (E3 P))
    (c : (E3 P).Store (CanonHost (E3 P))) : Prop :=
  ∃ (fid : FuncId) (a : (E3 P).FuncAddr) (p : FuncTy) (ys : List Flat),
    (E3 P).status yc.1 yc.2 = .callout (.lowered fid (witFt p) {} ⟨2⟩) ys ∧
    ArenaField.funcs.get? B.store fid = some (.lifted a (witFt p) {} ⟨1⟩) ∧
    p.results.length ≤ 1 ∧
    ((liftArgs p.params ys = none ∧ c = yc.1) ∨
      ∃ ws e, liftArgs p.params ys = some ws ∧
        Relation.ReflTransGen (CoreStep (E3 P))
          (yc.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e ∧
        ((E3 P).status e.1 e.2 = .returned .trap ∨
          ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧
            liftArgs p.results zs = none) ∧ c = e.1)

/-- How the forward run of a round ends at the shared thread `yc`. -/
def RoundEnd (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ u : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P)))) (B : Machine.Config (E3 P) σ)
    (f : Ii.F.Op) (yc : CoreSt (E3 P)) (u₁ π₁ : Store Nat) (w : Ii.F.Ar f) : Prop :=
  (∃ (t' : STh) (r : Silmaril.Wasm.Execution.Core.Result),
    LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f yc (u₁, t') π₁ ∧
    Silmaril.Wasm.Game.ResultAt u₁ t' r ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w) ∨
  (∃ c, NestTrap B yc c ∧ LReady P l Ie Ii s₀ u₀ F₀ c u₁ π₁ ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) .trap = some w)

/-- **A specification round is a segmented run of the shared thread**, ending as `RoundEnd`. -/
theorem rounds_fwd {u : Store Nat} (S : LStat P l Ie Ii u F₀ B (ownOf s₀))
    {cs₀ : Store (CanonHost (E3 P))} {π₀ : Store Nat} (hR : LReady P l Ie Ii s₀ u₀ F₀ cs₀ u π₀)
    {w : Ii.F.Ar f} :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (y : CoreSt (E3 P)) (x : Store Nat × STh) (π π₁ u₁ : Store Nat),
      LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rs dss →
      Linked2.ExpRunT P l Ie π dss.flatten π₁ →
      Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f w)]) (.idle u₁) →
      ∃ (recs : List (LRec P)) (yc : CoreSt (E3 P)), LSeg B y recs yc ∧
        RoundEnd P l Ie Ii s₀ u₀ u F₀ B f yc u₁ π₁ w
  | [], dss, y, x, π, π₁, u₁, hI, hrel, hexp, hpath => by
    cases hrel
    cases hexp
    obtain ⟨s', t', r, run, final, hw, hq⟩ := path_ret_inv (by simpa [callMoves] using hpath)
    cases hq
    obtain ⟨yc, hy, hIc⟩ := LInv.reach_fwd S hI run
    exact ⟨[], yc, .done hy, .inl ⟨t', r, hIc, final, hw⟩⟩
  | ⟨e, v⟩ :: rs, dss₀, y, x, π, π₁, u₁, hI, hrel, hexp, hpath => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss, Silmaril.Wasm.Component.Reference.ImpRel
        l.imp Ii ⟨e, v⟩ ds ∧ List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii)
          rs dss ∧ dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs ++
      [.inr (.ans f w)]) (by simpa [callMoves] using hpath)
    obtain ⟨y₁, hy₁, hI₁⟩ := LInv.reach_fwd S hI run
    obtain ⟨nm, p, wi, xe, ys, E, a, hk, hw, hxe, hpx, hdx, hys, hst, hyty⟩ :=
      LInv.callout_fwd S hI₁ co op
    have hek := ifaceOp?_some op
    obtain ⟨nm', ft, A, hk', hA, hm⟩ := hd
    have hA' : payloadAnswer (Ii.imports.get e.1) A = v := hA
    have hft : ft = p := by
      rw [hek.1, hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      exact hk'.2.symm
    subst hft
    have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
      hek.2 ▸ filterMap_of_mapM hys
    have hmi : (nm, ft) ∈ l.imp.imports := List.mem_of_getElem? hk
    have hres : ft.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
    have hfl : ArenaField.funcs.get? B.store (l.wireFid k) =
        some (.lifted (Ie.addrs.getD xe.core 0) (witFt ft) {} ⟨1⟩) :=
      hpx ▸ S.lifted k wi xe hw hxe
    have hxm : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
    have hwl : wi < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
    have hxw : l.exp.exports[(⟨wi, hwl⟩ : Fin l.exp.exports.length)] = xe :=
      (List.getElem?_eq_some_iff.mp hxe).2
    rw [hfilt] at hm
    split at hm
    · -- the arguments do not lift
      next hws =>
      obtain ⟨rfl, rfl⟩ := hm
      have hv : v = .trap := hA.symm
      subst hv
      obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
      cases hrel'
      cases hexp
      exact ⟨[], y₁, .done hy₁, .inr ⟨y₁.1, ⟨l.wireFid k, _, ft, ys, hst, hfl, hres,
        .inl ⟨hws, rfl⟩⟩, lready_after hR hI₁, hw'⟩⟩
    · next ws hws =>
      obtain ⟨hkl, R, rfl, hAR⟩ := hm
      have hexp' : Linked2.ExpRunT P l Ie π
          (⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten) π₁ := by
        simpa only [List.flatten_cons, List.singleton_append] using hexp
      cases hexp' with
      | @ret _ π₂ _ _ _ us _ w₂ hwire hRet hrest =>
        have hw₂ : w₂.val = wi := by
          rw [hek.1, hw] at hwire
          exact (Option.some.inj hwire).symm
        have hx₂ : l.exp.exports[w₂] = xe :=
          (List.getElem?_eq_some_iff.mp (hw₂.symm ▸ hxe : l.exp.exports[w₂.val]? = some xe)).2
        rw [hx₂] at hRet
        obtain ⟨ev, zs, hrunA, hstA, husA, hI₂⟩ :=
          LInv.resume_fwd S hI₁ (hpx ▸ hk) hxe hdx op hRet
        have hcheck : ValTy.checkList ft.results us = true :=
          Silmaril.Wasm.Component.checkList_of_liftArgs (hpx ▸ husA)
        have hv : Silmaril.Wasm.Game.Answer.toResult v =
            .values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
          rw [← hA', hAR, hpx]
          have hup : (some (Payload.vals us)).bind (Silmaril.Wasm.Component.Adapter.lower ft).up =
              some (.flat (lowerArgs ft.results us)) := by
            simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
              Silmaril.Wasm.Component.checkLower, hcheck, ite_true, Option.map_some]
          rw [hup, payloadAnswer_flat (w := .values ⟨_, resAnswer S hk hek.1 hcheck⟩) rfl]
          rfl
        rw [hv] at hpath'
        obtain ⟨recs, yc, hseg, hend⟩ := rounds_fwd S hR rs dss _ _ _ π₁ u₁ hI₂ hrel' hrest
          hpath'
        refine ⟨_, yc, .call hy₁ hst hfl hres hws (hpx ▸ hrunA) hstA (hpx ▸ husA)
          (hpx ▸ hseg), hend⟩
      | trap w₂ hwire hT hrest =>
        have hw₂ : w₂.val = wi := by
          rw [hek.1, hw] at hwire
          exact (Option.some.inj hwire).symm
        have hx₂ : l.exp.exports[w₂] = xe :=
          (List.getElem?_eq_some_iff.mp (hw₂.symm ▸ hxe : l.exp.exports[w₂.val]? = some xe)).2
        rw [hx₂] at hT
        have hv : v = .trap := by
          rw [← hA', hAR]
          rfl
        subst hv
        obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
        cases hrel'
        cases hrest
        obtain ⟨ev, hrunA, hendA, hRdy⟩ := LInv.expTrap_fwd S hR hI₁ hxm hT
        refine ⟨[], y₁, .done hy₁, .inr ⟨ev.1, ⟨l.wireFid k, _, ft, ys, hst, hfl, hres,
          .inr ⟨ws, ev, hws, hpx ▸ hrunA, ?_, rfl⟩⟩, hRdy, hw'⟩⟩
        rcases hendA with h | ⟨zs, h, -, hn⟩
        · exact .inl h
        · exact .inr ⟨zs, h, hpx ▸ hn⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
