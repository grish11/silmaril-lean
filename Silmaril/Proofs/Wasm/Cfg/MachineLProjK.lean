module

public import Silmaril.Proofs.Wasm.Cfg.MachineLProjX
public import Silmaril.Wasm.Interp.EHSim.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLProjI
import Silmaril.Proofs.Wasm.Cfg.MachineLProjC
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd
import Silmaril.Proofs.Wasm.Cfg.MachineLClosed
import Silmaril.Proofs.Wasm.Cfg.MachineLProjS
import Silmaril.Proofs.Wasm.Cfg.MachineLProjE
import Silmaril.Proofs.Wasm.Cfg.Region
import Silmaril.Proofs.Wasm.Cfg.MachineLBwd
import Silmaril.Proofs.Wasm.Cfg.MachineComplete

@[expose] public section

/-!
# Handlers: the checker invariant and the stepwise projection with `try_table` (proofs)

The checker invariant and the stepwise projection of `MachineLProjI`/`MachineLProjX` without the
`NoTry` restriction. A caught exception branches to the clause's label with at least its arity
(`catch_arity`, from the frame's recorded clause check and Interp's `catches_count` under the tag
invariants).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjK

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg.Proofs.MachineLProjI
open Silmaril.Wasm.Interp (ehExt chkE endsAt ExtArity)

variable {H : Type}

/-- **A caught exception meets its clause label's arity**: at a checked state, a `try_table`
frame `j` catching with values `us` and label `l` branches to a frame `L'` of arity at most
`us.length`. -/
theorem catch_arity {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {rp : List SeqStep} {ls : List LFrame} {out : Option Nat}
    (hF : ChkF (Interp.ehExt tags) F mi nl ret body rp ls out) {s : Store H} {f : Frame}
    (hE : Interp.ExnsOk tags s) (hf : f.module = mi) {j a : Nat} {L L' : LFrame}
    {us : List Val} {l : LabelIdx} (hL : ls[j]? = some L) (hT : L.tryT = true)
    (hc : Catches s f a L.catches (some (us, l))) (hL' : ls[j + 1 + l.toNat]? = some L') :
    L'.arity ≤ us.length := by
  have hk : j < ls.length := (List.getElem?_eq_some_iff.mp hL).1
  obtain ⟨outk, hFk⟩ := chkF_drop j _ _ out (by omega) hF
  have hdl : ls.drop j = L :: ls.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hk]; congr 1; exact (List.getElem?_eq_some_iff.mp hL).2
  rw [hdl] at hFk
  rcases hdr : rp.drop j with _ | ⟨⟨m, b⟩, rp'⟩
  · rw [hdr] at hFk; exact hFk.elim
  rw [hdr] at hFk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcat, -⟩ := hFk
  obtain ⟨ns, hext, hok⟩ := hcat hT
  simp only [Interp.ehExt, Option.map_eq_some_iff] at hext
  obtain ⟨ns', hns, hns'⟩ := hext
  cases hns'
  subst hf
  obtain ⟨n, hn, hle⟩ := Interp.catches_count hE hc hns hok
  have hl' : l.toNat < (ls.drop (j + 1)).length := by
    have := (List.getElem?_eq_some_iff.mp hL').1; simp; omega
  have hlk : (labs ret (ls.drop (j + 1)))[l.toNat]? = some L'.arity := by
    rw [labs, List.getElem?_append_left (by simpa using hl'), List.getElem?_map,
      List.getElem?_drop, show j + 1 + l.toNat = j + 1 + l.toNat from rfl, hL']; rfl
  rw [hlk] at hn; cases hn; exact hle

open Silmaril.Wasm.Abstract.ExposePTyped (GoodO) in
/-- **Dispatching a checked outcome**, `try_table` included: a caught exception branches to a
label whose arity its values meet. -/
theorem disp_invE {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × Abstract.CallXP.POut}
    {st' : MState H} {c : List Instr} {out oc : Option Nat}
    (hd : DispL body b ls r st') (hf : r.2.1.module = mi) (hok : FramesOk body b.seq.reverse ls)
    (hc : seqAt body b.seq = some c) (hF : ChkF ext F mi nl ret body b.seq.reverse ls out)
    (hgo : GoodO (labs ret ls) ret oc r.2.2)
    (hnext : ∀ ws, r.2.2 = .flow (.normal ws) → oc = some ws.length →
      chkE ext F mi nl ret (labs ret ls) (some ws.length) (liftInstrs (restAt c (b.idx + 1))) =
        some out)
    (hcat : ∀ (j a : Nat) (L L' : LFrame) (us : List Val) (l : LabelIdx), ls[j]? = some L →
      L.tryT = true → Catches r.1 r.2.1 a L.catches (some (us, l)) →
      ls[j + 1 + l.toNat]? = some L' → L'.arity ≤ us.length) :
    CInv ext F mi nl ret body st' := by
  cases hd with
  | @next s f ws st' hg =>
    simp only [GoodO] at hgo
    have hchk := hnext ws rfl hgo
    obtain ⟨hfit, hinv⟩ := entry_inv (s := s) (W := ws.reverse) hf hc (by simpa using hchk) hF
    rw [MachineLProjC.gotoN_eq_goto hfit] at hg
    cases hg; exact hinv
  | @br s f ws k L st' hL hg =>
    simp only [GoodO] at hgo
    obtain ⟨n, hn, hle⟩ := hgo
    have hk : k < ls.length := (List.getElem?_eq_some_iff.mp hL).1
    have hlk : (labs ret ls)[k]? = some L.arity := by
      rw [labs, List.getElem?_append_left (by simpa using hk), List.getElem?_map, hL]; rfl
    have hn' : n = L.arity := by
      rw [hlk] at hn; exact (Option.some.inj hn).symm
    subst hn'
    obtain ⟨hg', hinv⟩ := branch_inv (s := s) hf hok hF hL hle
    rw [hg'] at hg; cases hg; exact hinv
  | brOut => simp [CInv]
  | ret => simp [CInv]
  | trap => simp [CInv]
  | raise => simp [CInv]
  | @catch_ s f a j us L L' l st' _ hL hT hc hL' hg =>
    have hN : L'.arity ≤ (us.reverse ++ L.outer.reverse).length := by
      have := hcat j a L L' us l hL hT hc hL'; simp; omega
    obtain ⟨hg', hinv⟩ := branch_inv (s := s) hf hok hF hL' hN
    rw [hg'] at hg; cases hg; exact hinv
  | catchOut => simp [CInv]

open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
open Silmaril.Wasm.Abstract.ExposePStruct (Ctx) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
/-- **The checker invariant is preserved by logged steps**, `try_table` included. -/
theorem cinv_stepE {Γ : Ctx H} {C : Abstract.CallRel H} (hC : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' := by
  cases hs with
  | @run b sg stk ls s f l r st' hb ht hr hd =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c', hc', hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc'; cases hc'
    simp only at hchk
    rw [restAt_cons hsg, Binaryen.liftInstrs_append, chkE_append] at hchk
    obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
    have d := Proofs.MachineLClosed.logged_closed hr hl
    obtain ⟨s', f', o⟩ := r
    simp only at hg hn hf
    have hoc' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs (codeOf sg)) = some oc := by
      rw [hg.1, hf, hn, List.length_reverse]; exact hoc
    obtain ⟨hg', hf', hn', hgo⟩ := evalOXP_goodO hC d hg hoc'
    obtain ⟨hs1, hs2⟩ := disp_sf hd
    simp only at hs1 hs2
    refine ⟨by rw [hs1]; exact hg', by rw [hs2, hn', hn], ?_⟩
    exact disp_invE hd (by simp only; rw [hf', hf]) (by simpa [MInv] using hok) hc hF hgo
      (fun ws hw hoc2 => by simp only at hw; subst hw; subst hoc2; exact hrest)
      (fun j a L L' us l hL hT hc hL' => catch_arity hF hg'.2.2 (by simp only; rw [hf', hf]) hL hT hc
        hL')
  | @abort b sg stk ls s f l r st' hb hr hnn hd =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c', hc', hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc'; cases hc'
    simp only at hchk
    rw [restAt_cons hsg, Segment.instrs, List.append_assoc, Binaryen.liftInstrs_append, chkE_append]
      at hchk
    obtain ⟨oc, hoc, -⟩ := Option.bind_eq_some_iff.mp hchk
    have d := Proofs.MachineLClosed.logged_closed hr hl
    obtain ⟨s', f', o⟩ := r
    simp only at hg hn hf
    have hoc' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
      rw [hg.1, hf, hn, List.length_reverse]; exact hoc
    obtain ⟨hg', hf', hn', hgo⟩ := evalOXP_goodO hC d hg hoc'
    obtain ⟨hs1, hs2⟩ := disp_sf hd
    simp only at hs1 hs2
    refine ⟨by rw [hs1]; exact hg', by rw [hs2, hn', hn], ?_⟩
    exact disp_invE hd (by simp only; rw [hf', hf]) (by simpa [MInv] using hok) hc hF hgo
      (fun ws hw _ => by simp only at hw; subst hw; exact absurd trivial hnn)
      (fun j a L L' us l hL hT hc hL' => catch_arity hF hg'.2.2 (by simp only; rw [hf', hf]) hL hT hc
        hL')
  | @enter b sg stk V V' ls s s₁ f f₁ i a c' bt np nr loop tryT cs l st' hb ht harm hkind hr hsel
      har hg' =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc₀; cases hc₀
    simp only at hchk
    rw [restAt_cons hsg, Segment.instrs, ht, Option.toList_some, List.append_assoc,
      Binaryen.liftInstrs_append, chkE_append] at hchk
    obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
    have d := Proofs.MachineLClosed.logged_closed hr hl
    simp only at hg hn hf
    have hoc' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
      rw [hg.1, hf, hn, List.length_reverse]; exact hoc
    obtain ⟨hg', hf', hn', hgo⟩ := evalOXP_goodO hC d hg hoc'
    simp only [GoodO] at hgo
    subst hgo
    have hf₁ : f₁.module = mi := by rw [hf', hf]
    simp only [liftInstrs, List.singleton_append, chkE, Option.bind_eq_some_iff] at hrest
    obtain ⟨o₂, h₂, hrest⟩ := hrest
    obtain ⟨np', nr', hba, hle, ho₂, ⟨oa, hoa, hoaE⟩, hcat'⟩ := chk_structE hkind hsel harm h₂
    rw [arity_eq_blockArity hf₁, hba] at har
    simp only [Option.some.injEq, Prod.mk.injEq] at har
    obtain ⟨rfl, rfl⟩ := har
    subst ho₂
    set L : LFrame := ⟨if loop then np' else nr', (V'.drop np').reverse, loop, tryT, cs, bt⟩
      with hLdef
    have hcA : seqAt body (b.seq ++ [(b.idx, a)]) = some c' := by
      rw [Proofs.Machine.seqAt_append]; simp [hc, hsg, ht, harm]
    have hFa : ChkF (ehExt Γ.tags) Γ.funcs mi nl ret body (b.seq ++ [(b.idx, a)]).reverse
        (L :: ls) oa := by
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
      refine ⟨c, sg, i, c', np', nr', by simpa using hc, hsg, ht, harm, hkind, hba, rfl,
      fun h => hcat' h, hoaE,
        ⟨oa, hoa, hoaE⟩, out, ?_, hF⟩
      have : (L.outer.length + nr') = V'.length - np' + nr' := by simp [hLdef]
      rw [this]; exact hrest
    have hW : ((V'.take np').reverse).length = np' := by simp; omega
    obtain ⟨hfit, hinv⟩ := entry_inv (s := s₁) (W := (V'.take np').reverse) hf₁ (j := 0) hcA
      (by rw [restAt_zero, hW]; exact hoa) hFa
    have hlen : (b.seq ++ [(b.idx, a)]).length = b.seq.length + 1 := by simp
    rw [hlen] at hfit hinv
    rw [MachineLProjC.gotoN_eq_goto hfit] at hg'
    cases hg'
    exact ⟨hg', by simp [goto]; rw [hn', hn], hinv⟩


open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **The checker invariant along logged runs**, `try_table` included. -/
theorem cinv_runE {Γ : Abstract.ExposePStruct.Ctx H} {C : Abstract.CallRel H} (hC : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {st st' : MState H}
    {l : List (Abstract.SCall H)} (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' := by
  induction h with
  | refl => exact ⟨hg, hn, hI⟩
  | step hs _ ih =>
    obtain ⟨hg₁, hn₁, hI₁⟩ := cinv_stepE hC hs (fun e he => hl e (List.mem_append_left _ he))
      hok hg hn hI
    exact ih (fun e he => hl e (List.mem_append_right _ he)) (MachineLFwd.mstep_ok hs hok) hg₁
      hn₁ hI₁

section Proj
variable {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
  {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat} {body : Expr}
open Silmaril.Wasm.Cfg.Proofs.MachineLProjT

/-- **A caught exception, native and `MStepC`**: the native branch to the clause's label is
the `MStepC` catch rule's target (supplied as `hrule`), the caught values meeting the label's
arity. -/
theorem catch_proj {b : BlockId} {stk : List Val} {ls : List LFrame} {s s₀ : Store H}
    {f f₀ : Frame} {j : Nat} {L L' : LFrame} {us : List Val} {l : LabelIdx} {st' : MState H}
    {out : Option Nat}
    (hg : branchN body b ls (j + 1 + l.toNat) L' (us.reverse ++ L.outer.reverse) s f = some st')
    (hf : f.module = mi) (hok : FramesOk body b.seq.reverse ls)
    (hF : ChkF ext F mi nl ret body b.seq.reverse ls out) (hL' : ls[j + 1 + l.toNat]? = some L')
    (har : L'.arity ≤ us.length)
    (hrule : L'.arity ≤ (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)).length →
      (L'.loop = true → ∃ t₁ t₂, f.module.blockType? L'.bt = some (t₁, t₂) ∧
        t₁.length = L'.arity) →
      MStepC P host C body ⟨.block b, stk, ls, s₀, f₀⟩
        (if L'.loop then
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat)) (L' :: ls.drop (j + 1 + l.toNat + 1))
            (topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s f
        else
          goto ((labels body b.seq).getD (j + 1 + l.toNat) .invalid)
            (b.seq.length - (j + 1 + l.toNat + 1)) (ls.drop (j + 1 + l.toNat + 1))
            (L'.outer ++ topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s f)) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s₀, f₀⟩ stC ∧ ProjRel st' stC := by
  set N := us.reverse ++ L.outer.reverse with hN
  have hNr : N.reverse = L.outer ++ us := by simp [hN]
  have hle : L'.arity ≤ N.length := by simp [hN]; omega
  obtain ⟨hg', -⟩ := branch_inv (s := s) hf hok hF hL' hle
  rw [hg'] at hg; cases hg
  have harity : L'.arity ≤ (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)).length := by
    obtain ⟨jk, hjk⟩ := MachineLProjC.brVals_junk l.toNat (ls.drop (j + 1)) (L.outer ++ us)
    rw [hjk]; simp; omega
  have hlbt : L'.loop = true → ∃ t₁ t₂, f.module.blockType? L'.bt = some (t₁, t₂) ∧
      t₁.length = L'.arity := by
    intro hloop
    obtain ⟨np, nr, hba, hLa⟩ := frame_at hF hL'
    obtain ⟨t₁, t₂, hbt, h1, -⟩ := blockType_of_blockArity hba
    rw [hloop] at hLa
    exact ⟨t₁, t₂, by rw [hf]; exact hbt, by rw [h1, hLa]; rfl⟩
  refine ⟨_, hrule harity hlbt, .inl ?_⟩
  have h1 : topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)) =
      topVals L'.arity (brVals (j + 1 + l.toNat) ls N.reverse) := by
    rw [← hNr, MachineLProjC.topVals_brVals hle, MachineLProjC.topVals_brVals hle]
  rw [h1]

/-- **An abrupt segment body**, `try_table` included: a trap or an uncaught exception is
`bodyTrap`/`bodyRaise`; a caught exception is `bodyCatch`/`bodyCatchOut`. -/
theorem abrupt_projE {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {o₁ : Region.Out} {fl : Flow} {st' : MState H}
    {out : Option Nat} (hb : lookup body b = some sg)
    (hbody : RunC P host C s f stk (expression sg.body) s₁ f₁ o₁) (hfl : OutFlat o₁)
    (hn : ∀ W, o₁ ≠ .normal W) (hfr : Bridge.FlowRel fl o₁)
    (hd : DispL body b ls (s₁, f₁, .flow fl) st') (hf : f₁.module = mi)
    (hok : FramesOk body b.seq.reverse ls) (hF : ChkF ext F mi nl ret body b.seq.reverse ls out)
    (hcat : ∀ (j a : Nat) (L L' : LFrame) (us : List Val) (l : LabelIdx), ls[j]? = some L →
      L.tryT = true → Catches s₁ f₁ a L.catches (some (us, l)) →
      ls[j + 1 + l.toNat]? = some L' → L'.arity ≤ us.length) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  cases o₁ with
  | normal W => exact absurd rfl (hn W)
  | trap =>
    obtain rfl := flowRel_trap hfr
    cases hd
    exact ⟨_, .bodyTrap hb hbody, .inl rfl⟩
  | throw a =>
    obtain rfl := flowRel_throw hfr
    cases hd with
    | raise hT => exact ⟨_, .bodyRaise hb hbody hT, .inl rfl⟩
    | @catch_ _ _ _ j us L L' l _ hpass hL hT hc hL' hg =>
      exact catch_proj hg hf hok hF hL' (hcat j a L L' us l hL hT hc hL')
        (fun ha hl => .bodyCatch hb hbody hpass hL hT hc hL' ha hl)
    | @catchOut _ _ _ j us L l hpass hL hT hc hout =>
      refine ⟨_, .bodyCatchOut hb hbody hpass hL hT hc hout,
        .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
      exact MachineLProjC.brVals_junk l.toNat (ls.drop (j + 1)) (L.outer ++ us)
  | _ => exact hfl.elim

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chk_structE arity_eq_blockArity entry_inv) in
open Silmaril.Wasm.Cfg.Proofs.MachineLProjX (dispL_flow runC_body_out term_runE flowRel_tailNull
  not_flowRel_tail) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **A logged block step without a structured terminator**, `try_table` included. -/
theorem proj_runK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l : List (Abstract.SCall H)} {r : Store H × Frame × Abstract.CallXP.POut} {st' : MState H}
    (hb : lookup body b = some sg) (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i)
    (hr : Abstract.EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l r)
    (hd : DispL body b ls r st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : FramesOk body b.seq.reverse ls) (hg : Γ.Good s) (hn : f.locals.length = nl)
    (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body ⟨.block b, stk, ls, s, f⟩) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Binaryen.liftInstrs_append, chkE_append] at hchk
  obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
  have hoc' : Interp.chkE (Interp.ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
      (some stk.reverse.length) (liftInstrs (codeOf sg)) = some oc := by
    rw [hg.1, hf, hn, List.length_reverse]; exact hoc
  have hbodyNT : ∀ i ∈ sg.body, isTerminator i = false := (MachineLBwd.seg_wf hsg).1
  have hflat : ∀ i ∈ codeOf sg, liftInstr i = .op i [] := by
    intro i hi
    simp only [MachineL.codeOf, List.mem_append] at hi
    rcases hi with hi | hi
    · exact MachineLProjS.liftInstr_flat (hbodyNT i hi)
    · cases htt : sg.term with
      | none => simp [htt] at hi
      | some t => simp [htt] at hi; subst hi; exact liftInstr_of_not_struct (ht _ htt)
  have d := Proofs.MachineLClosed.logged_closed hr hl
  obtain ⟨hgE, hf', -, hgo⟩ := evalOXP_goodO hA d hg hoc'
  obtain ⟨s₂, f₂, fl, rfl⟩ := dispL_flow hd
  obtain ⟨s', f', o, hrun, hs', hf'', hfr⟩ :=
    MachineLProjE.flat_runP (P := P) (host := host) hA hflat d hg hoc'
  simp only at hf' hgo
  subst hs' hf''
  rw [List.reverse_reverse] at hrun
  have hf₂ : f₂.module = mi := by rw [hf', hf]
  have hcatS : ∀ (j a : Nat) (L L' : LFrame) (us : List Val) (l : LabelIdx), ls[j]? = some L →
      L.tryT = true → Catches s₂ f₂ a L.catches (some (us, l)) →
      ls[j + 1 + l.toNat]? = some L' → L'.arity ≤ us.length :=
    fun j a L L' us l hL hT hc hL' => catch_arity hF hgE.2.2 hf₂ hL hT hc hL'
  rw [show expression (codeOf sg) = expression sg.body ++ expression sg.term.toList by
    simp [MachineL.codeOf, expression]] at hrun
  obtain ⟨s₁, f₁, o₁, hbody, hthen⟩ := Proofs.Region.run_split hrun rfl
  have hbo := runC_body_out hbodyNT hbody
  cases hterm : sg.term with
  | none =>
    simp only [hterm, Option.toList_none, expression, List.map_nil] at hthen
    obtain ⟨rfl, rfl, rfl⟩ := thenC_nil hthen
    by_cases hnorm : ∃ W, o = .normal W
    · obtain ⟨W, rfl⟩ := hnorm
      obtain ⟨ws, rfl, rfl⟩ := flowRel_normal hfr
      simp only [GoodO] at hgo
      subst hgo
      have := next_target hd hf₂ hc (by simpa [Segment.instrs, hterm] using hrest) hF
      exact ⟨_, .fall hb hterm hbody, .inl this.symm⟩
    · exact abrupt_projE hb hbody hbo (fun W h => hnorm ⟨W, h⟩) hfr hd hf₂ hok hF hcatS
  | some t =>
    have hrest' : ∀ h, oc = some h → Interp.chkE (Interp.ehExt Γ.tags) Γ.funcs mi nl ret
        (labs ret ls) (some h) (liftInstrs (restAt c (b.idx + 1))) = some out := by
      intro h hh; subst hh; exact hrest
    simp only [hterm, Option.toList_some, expression, List.map_cons, List.map_nil] at hthen
    cases o₁ with
    | normal stk₁ =>
      change RunC P host C s₁ f₁ stk₁ [.plain t] s₂ f₂ o at hthen
      rcases term_runE hsg hterm (ht t hterm) hthen with
        rfl | ⟨hthr, a, rfl⟩ | ⟨htc, ⟨W, c', rfl⟩ | ⟨W, a, c', rfl⟩⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨l', rfl, rfl, rfl, rfl⟩ | ⟨l', k, W, rfl, rfl, hk, rfl, rfl⟩ |
        ⟨ws, us, us', X, rfl, hbs, hX, rfl, rfl⟩
      · obtain rfl := flowRel_trap hfr
        cases hd
        exact ⟨_, .termTrap hb hterm hbody hthen, .inl rfl⟩
      · obtain rfl := flowRel_throw hfr
        cases hd with
        | raise hT => exact ⟨_, .raise hb hterm hthr hbody hthen hT, .inl rfl⟩
        | @catch_ _ _ _ j us L L' l _ hpass hL hT hc hL' hg =>
          exact catch_proj hg hf₂ hok hF hL' (hcatS j a L L' us l hL hT hc hL')
            (fun ha hl => .catch_ hb hterm hthr hbody hthen hpass hL hT hc hL' ha hl)
        | @catchOut _ _ _ j us L l hpass hL hT hc hout =>
          refine ⟨_, .catchOut hb hterm hthr hbody hthen hpass hL hT hc hout,
            .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
          exact MachineLProjC.brVals_junk l.toNat (ls.drop (j + 1)) (L.outer ++ us)
      · obtain rfl := flowRel_tailNull hfr
        cases hd
        exact ⟨_, .tailNull hb hterm htc hbody hthen, .inl rfl⟩
      · exact absurd hfr not_flowRel_tail
      · obtain ⟨ws, junk, rfl, rfl⟩ := flowRel_ret hfr
        cases hd
        refine ⟨_, .ret hb hterm hbody, .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
        obtain ⟨j, hj⟩ := MachineLProjC.brVals_junk ls.length ls (junk ++ ws.reverse)
        exact ⟨j ++ junk, by rw [hj, List.append_assoc]⟩
      · obtain ⟨ws, junk, rfl, rfl⟩ := flowRel_br hfr
        exact br_proj hd hf₂ hok hF hgo rfl rfl
          (fun L hL ha hlbt => .br hb hterm hbody hL ha hlbt)
          (fun h => .brOut hb hterm hbody h)
      · rcases hk with ⟨rfl, rfl⟩ | ⟨hk, rfl⟩
        · obtain ⟨ws, rfl, rfl⟩ := flowRel_normal hfr
          simp only [GoodO] at hgo
          have := next_target hd hf₂ hc (hrest' _ hgo) hF
          exact ⟨_, .brIfNot hb hterm hbody, .inl this.symm⟩
        · obtain ⟨ws, junk, rfl, rfl⟩ := flowRel_br hfr
          exact br_proj hd hf₂ hok hF hgo rfl rfl
            (fun L hL ha hlbt => .brIfTaken hb hterm hbody hk hL ha hlbt)
            (fun h => .brIfOut hb hterm hbody hk h)
      · rcases hX with ⟨rfl, rfl⟩ | ⟨l', rfl, rfl⟩
        · obtain ⟨ws', hws, hW⟩ := flowRel_normal hfr
          subst hws
          simp only [GoodO] at hgo
          have := next_target hd hf₂ hc (hrest' _ hgo) hF
          refine ⟨_, .brDataNot hb hterm hbody hbs, .inl ?_⟩
          rw [this, hW]
        · obtain ⟨ws', junk, rfl, hW⟩ := flowRel_br hfr
          exact br_proj hd hf₂ hok hF hgo hW rfl
            (fun L hL ha hlbt => .brDataTaken hb hterm hbody hbs hL ha hlbt)
            (fun h => .brDataOut hb hterm hbody hbs h)
    | trap =>
      obtain ⟨rfl, rfl, rfl⟩ := hthen
      exact abrupt_projE hb hbody hbo (fun W h => by cases h) hfr hd hf₂ hok hF hcatS
    | throw a =>
      obtain ⟨rfl, rfl, rfl⟩ := hthen
      exact abrupt_projE hb hbody hbo (fun W h => by cases h) hfr hd hf₂ hok hF hcatS
    | _ => exact hbo.elim

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chk_structE arity_eq_blockArity entry_inv) in
open Silmaril.Wasm.Cfg.Proofs.MachineLProjX (dispL_flow runC_body_out term_runE flowRel_tailNull
  not_flowRel_tail) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **An abrupt segment before a structured terminator**, `try_table` included. -/
theorem proj_abortK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l : List (Abstract.SCall H)} {r : Store H × Frame × Abstract.CallXP.POut} {st' : MState H}
    (hb : lookup body b = some sg)
    (hr : Abstract.EvalLXPS s f stk.reverse (liftInstrs sg.body) l r) (hnn : ¬ r.2.2.IsNormal)
    (hd : DispL body b ls r st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : FramesOk body b.seq.reverse ls) (hg : Γ.Good s)
    (hn : f.locals.length = nl)
    (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body ⟨.block b, stk, ls, s, f⟩) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Segment.instrs, List.append_assoc, Binaryen.liftInstrs_append, chkE_append]
    at hchk
  obtain ⟨oc, hoc, -⟩ := Option.bind_eq_some_iff.mp hchk
  have hoc' : Interp.chkE (Interp.ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
      (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
    rw [hg.1, hf, hn, List.length_reverse]; exact hoc
  have hbodyNT : ∀ i ∈ sg.body, isTerminator i = false := (MachineLBwd.seg_wf hsg).1
  have hflat : ∀ i ∈ sg.body, liftInstr i = .op i [] :=
    fun i hi => MachineLProjS.liftInstr_flat (hbodyNT i hi)
  have d := Proofs.MachineLClosed.logged_closed hr hl
  obtain ⟨hgE, hf', -, -⟩ := evalOXP_goodO hA d hg hoc'
  obtain ⟨s₂, f₂, fl, rfl⟩ := dispL_flow hd
  obtain ⟨s', f', o, hrun, hs', hf'', hfr⟩ := MachineLProjE.flat_runP (P := P) (host := host) hA
    hflat d hg hoc'
  subst hs' hf''
  rw [List.reverse_reverse] at hrun
  have hbo := runC_body_out hbodyNT hrun
  simp only at hf' hgE
  have hf₂ : f₂.module = mi := by rw [hf', hf]
  refine abrupt_projE hb hrun hbo (fun W h => ?_) hfr hd hf₂ hok hF
    (fun j a L L' us l hL hT hc hL' => catch_arity hF hgE.2.2 hf₂ hL hT hc hL')
  subst h
  obtain ⟨ws, rfl, -⟩ := flowRel_normal hfr
  exact hnn trivial

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chk_structE arity_eq_blockArity entry_inv) in
open Silmaril.Wasm.Cfg.Proofs.MachineLProjX (dispL_flow runC_body_out term_runE flowRel_tailNull
  not_flowRel_tail) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **Entering an arm**, `try_table` included. -/
theorem proj_enterK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C)
    {mi : ModuleInst} {nl ret : Nat} {body : Expr} {b : BlockId} {sg : Segment}
    {stk V V' : List Val} {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {i : Instr}
    {a : Nat} {c' : List Instr} {bt : BlockType} {np nr : Nat} {loop tryT : Bool}
    {cs : List Catch} {l : List (Abstract.SCall H)} {st' : MState H}
    (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c')
    (hkind : StructKind i bt loop tryT cs)
    (hr : Abstract.EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal V)))
    (hsel : ArmSel i V a V') (har : Binaryen.arity f₁ bt = some (np, nr))
    (hg' : gotoN (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s₁ f₁ = some st')
    (hl : ∀ e ∈ l, CloseOk C e) (hg : Γ.Good s) (hn : f.locals.length = nl)
    (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body ⟨.block b, stk, ls, s, f⟩) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Segment.instrs, ht, Option.toList_some, List.append_assoc,
    Binaryen.liftInstrs_append, chkE_append] at hchk
  obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
  have hoc' : Interp.chkE (Interp.ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
      (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
    rw [hg.1, hf, hn, List.length_reverse]; exact hoc
  have hbodyNT : ∀ i ∈ sg.body, isTerminator i = false := (MachineLBwd.seg_wf hsg).1
  have hflat : ∀ i ∈ sg.body, liftInstr i = .op i [] :=
    fun i hi => MachineLProjS.liftInstr_flat (hbodyNT i hi)
  have d := Proofs.MachineLClosed.logged_closed hr hl
  obtain ⟨-, hf', -, hgo⟩ := evalOXP_goodO hA d hg hoc'
  simp only [GoodO] at hgo hf'
  subst hgo
  obtain ⟨s', f', o, hrun, hs', hf'', hfr⟩ :=
    MachineLProjE.flat_runP (P := P) (host := host) hA hflat d hg hoc'
  subst hs' hf''
  rw [List.reverse_reverse] at hrun
  have hoN : o = .normal V.reverse := by
    cases o <;> simp_all [Bridge.FlowRel]
  subst hoN
  have hf₁ : f₁.module = mi := by rw [hf', hf]
  simp only [liftInstrs, List.singleton_append, Interp.chkE, Option.bind_eq_some_iff] at hrest
  obtain ⟨o₂, h₂, hrest⟩ := hrest
  obtain ⟨np', nr', hba, hle, ho₂, ⟨oa, hoa, hoaE⟩, hcat'⟩ := chk_structE hkind hsel harm h₂
  rw [arity_eq_blockArity hf₁, hba] at har
  simp only [Option.some.injEq, Prod.mk.injEq] at har
  obtain ⟨rfl, rfl⟩ := har
  subst ho₂
  obtain ⟨t₁, t₂, hbt, h1, h2⟩ := blockType_of_blockArity hba
  obtain ⟨hcond, hus⟩ := MachineLProjC.armSel_condArm hsel hle
  set L : LFrame := ⟨if loop then np' else nr', (V'.drop np').reverse, loop, tryT, cs, bt⟩
    with hLdef
  have hcA : seqAt body (b.seq ++ [(b.idx, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hc, hsg, ht, harm]
  have hFa : ChkF (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body (b.seq ++ [(b.idx, a)]).reverse
      (L :: ls) oa := by
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
    refine ⟨c, sg, i, c', np', nr', by simpa using hc, hsg, ht, harm, hkind, hba, rfl,
      fun h => hcat' h, hoaE,
      ⟨oa, hoa, hoaE⟩, out, ?_, hF⟩
    have : (L.outer.length + nr') = V'.length - np' + nr' := by simp [hLdef]
    rw [this]; exact hrest
  have hW : ((V'.take np').reverse).length = np' := by simp; omega
  obtain ⟨hfit, -⟩ := entry_inv (s := s₁) (W := (V'.take np').reverse) hf₁ (j := 0) hcA
    (by rw [restAt_zero, hW]; exact hoa) hFa
  rw [show (b.seq ++ [(b.idx, a)]).length = b.seq.length + 1 by simp] at hfit
  rw [MachineLProjC.gotoN_eq_goto hfit] at hg'
  cases hg'
  have hlab := MachineLProjC.labelArity_eq loop (hf₁ ▸ hbt : f₁.module.blockType? bt = some _)
    (by rw [arity_eq_blockArity hf₁]; exact hba)
  refine ⟨_, .enter hb ht harm hkind hrun hcond (by rw [hf₁]; exact hbt) (by rw [hus, h1]), .inl ?_⟩
  rw [hlab]

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged step projects to one `MStepC` step**: exceptions on, every call form, `try_table`
included. -/
theorem proj_stepK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, MStepC P host C body st stC ∧ ProjRel st' stC := by
  cases hs with
  | run hb ht hr hd =>
    exact proj_runK hA hb ht hr hd hl (by simpa [MInv] using hok) hg hn hI
  | abort hb hr hnn hd => exact proj_abortK hA hb hr hnn hd hl (by simpa [MInv] using hok) hg hn hI
  | enter hb ht harm hkind hr hsel har hg' =>
    exact proj_enterK hA hb ht harm hkind hr hsel har hg' hl hg hn hI

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged run projects to an `MStepC` run**, step by step, `try_table` included. -/
theorem proj_runLK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {st st' : MState H}
    {l : List (Abstract.SCall H)} (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) st stC ∧ ProjRel st' stC := by
  induction h with
  | refl => exact ⟨_, .refl, .inl rfl⟩
  | @step st st₁ st₂ l₁ l₂ hs hr ih =>
    have hl₁ : ∀ e ∈ l₁, CloseOk C e := fun e he => hl e (List.mem_append_left _ he)
    have hl₂ : ∀ e ∈ l₂, CloseOk C e := fun e he => hl e (List.mem_append_right _ he)
    obtain ⟨stC₁, hC₁, hR₁⟩ := proj_stepK (P := P) (host := host) hA hs hl₁ hok hg hn hI
    obtain ⟨hg₁, hn₁, hI₁⟩ := cinv_stepE hA hs hl₁ hok hg hn hI
    rcases hR₁ with rfl | hR₁
    · obtain ⟨stC₂, hC₂, hR₂⟩ := ih hl₂ (MachineLFwd.mstep_ok hs hok) hg₁ hn₁ hI₁
      exact ⟨stC₂, .head hC₁ hC₂, hR₂⟩
    · obtain ⟨rfl, -⟩ := mrunL_sink hr (fun b h => by rw [hR₁.1] at h; cases h)
      exact ⟨stC₁, .single hC₁, .inr hR₁⟩

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged run from the CFG entry projects to an `MStepC` run from the CFG entry**:
exceptions on, every call form, `try_table` included. -/
theorem proj_initialK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {s : Store H}
    {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk C e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) (initial body s f) stC ∧ ProjRel st' stC :=
  proj_runLK hA h hl (MachineLFwd.initial_ok body s f) hg rfl
    (MachineLProjI.cinv_initial (s := s) (f := f) rfl hchk)

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged run from the CFG entry ending in an answered tail call** is an `MStepC` run to the
sink the answer stands for, `try_table` included. -/
theorem proj_tail_initialK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {s : Store H}
    {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l l' : List (Abstract.SCall H)} {st : MState H} {s₁ s₂ : Store H} {f₁ : Frame} {a n : Nat}
    {args : List Val} {b : (List Val ⊕ Nat) ⊕ PUnit.{1}}
    (h : MRunL body (initial body s f) l st) (ht : TailL body st l' (s₁, f₁, .tail a args n))
    (hl : ∀ e ∈ l ++ l', CloseOk C e) (he : CloseOk C (Abstract.SCall.mk a args s₁ b s₂)) :
    Relation.ReflTransGen (MStepC P host C body) (initial body s f) (tailSink b s₂ f₁) := by
  have hl₁ : ∀ e ∈ l, CloseOk C e := fun e he => hl e (List.mem_append_left _ he)
  have hl₂ : ∀ e ∈ l', CloseOk C e := fun e he => hl e (List.mem_append_right _ he)
  have hok := MachineLFwd.initial_ok body s f
  have hI₀ := MachineLProjI.cinv_initial (s := s) (f := f) rfl hchk
  obtain ⟨stC, hC, hR⟩ := proj_runLK (P := P) (host := host) hA h hl₁ hok hg rfl hI₀
  obtain ⟨hg', hn', hI'⟩ := cinv_runE hA h hl₁ hok hg rfl hI₀
  obtain ⟨bb, hbb⟩ := MachineLProjX.tailL_block ht
  rcases hR with rfl | hR
  · exact hC.tail (MachineLProjX.proj_tailE hA ht hl₂ he hg' hn' hI')
  · rw [hbb] at hR; cases hR.1

end Proj

end Silmaril.Wasm.Cfg.Proofs.MachineLProjK
