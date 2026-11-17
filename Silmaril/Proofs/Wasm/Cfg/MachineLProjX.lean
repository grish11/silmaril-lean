module

public import Silmaril.Proofs.Wasm.Cfg.MachineLProjT
public import Silmaril.Proofs.Wasm.Cfg.MachineLProjE
import Silmaril.Proofs.Wasm.Cfg.MachineComplete
import Silmaril.Proofs.Wasm.Cfg.MachineLClosed
import Silmaril.Proofs.Wasm.Cfg.Region
import Silmaril.Proofs.Wasm.Cfg.MachineLBwd
import Silmaril.Proofs.Wasm.Cfg.MachineLProjI
import Silmaril.Proofs.Wasm.Cfg.MachineLProjS
import Silmaril.Proofs.Wasm.Cfg.MachineLProjC
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd

@[expose] public section

/-!
# The stepwise projection over the pending, exception-aware semantics (proofs)

The stepwise projection of `MachineLProjT`, with the segment bridge `flat_runP` (`EvalOXP`, the
exception checker `ehExt`, every call form) in place of the legacy-semantics bridge: no
restriction on call forms (`DirectCalls`), no restriction to plain terminators (`PlainTerms`),
no `tExt` store check, no soundness hypothesis on the oracle beyond `ArityResp`. A `throw` or
`throw_ref` terminator is `MStepC.raise`; a tail call of null is `MStepC.tailNull`. The handler
case (`try_table`, `NoTry`) and the answered tail call (`TailL`, an end) are separate.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjX

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg.Proofs.MachineLProjT

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem rcr_plain {i : Instr} (h : (Admin.plain i).IsReturnCallRef) : ∃ y, i = .returnCallRef y := by
  cases i with
  | returnCallRef y => exact ⟨y, rfl⟩
  | _ => exact h.elim

theorem rcr_term {i : Instr} (h : (Admin.plain i).IsReturnCallRef) : isTerminator i = true := by
  obtain ⟨y, rfl⟩ := rcr_plain h; rfl

theorem rcr_tail {i : Instr} (h : (Admin.plain i).IsReturnCallRef) : i.IsTailCall := by
  obtain ⟨y, rfl⟩ := rcr_plain h; trivial

/-- **Straight-line code ends normally, in a trap or in a thrown exception**, every call form
included. -/
theorem runC_body_out : ∀ {is : List Instr}, (∀ i ∈ is, isTerminator i = false) →
    ∀ {s s' : Store H} {f f' : Frame} {vs : List Val} {o : Region.Out},
      RunC P host C s f vs (expression is) s' f' o → OutFlat o
  | [], _, _, _, _, _, _, _, h => by cases h; trivial
  | i :: is, hnt, s, s', f, f', vs, o, h => by
    have hi := hnt i (by simp)
    have ih := @runC_body_out is (fun j hj => hnt j (List.mem_cons_of_mem _ hj))
    simp only [expression, List.map_cons] at h
    cases h with
    | val _ h => exact ih h
    | simple _ _ h => exact ih h
    | simpleTrap => trivial
    | call _ _ _ _ _ h => exact ih h
    | callTrap => trivial
    | callThrow => trivial
    | callInd _ _ _ _ _ _ h => exact ih h
    | callIndTrap => trivial
    | callIndThrow => trivial
    | callIndRes => trivial
    | callRef _ _ _ _ _ h => exact ih h
    | callRefTrap => trivial
    | callRefThrow => trivial
    | callRefNull => trivial
    | brData hb => cases hb <;> simp [isTerminator] at hi
    | returnCallRef hc => exact absurd (rcr_term hc) (by rw [hi]; simp)
    | returnCallRefNull hc => exact absurd (rcr_term hc) (by rw [hi]; simp)
    | _ => simp [isTerminator] at hi

/-- **What a non-structured terminator's region run does**: it traps, throws (a `throw` or
`throw_ref`), ends in a tail call or a tail call of null (a tail-call form), returns, branches,
or falls through (an untaken `br_if` or data branch). -/
theorem term_runE {c : List Instr} {i : Nat} {sg : Segment} {t : Instr}
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t) (hns : ¬ Instr.IsStruct t)
    {s₁ s' : Store H} {f₁ f' : Frame} {stk₁ : List Val} {o : Region.Out}
    (h : RunC P host C s₁ f₁ stk₁ [.plain t] s' f' o) :
    o = .trap ∨
    (t.IsThrow ∧ ∃ a, o = .throw a) ∨
    (t.IsTailCall ∧ ((∃ W c, o = .tailNull W c) ∨ ∃ W a c, o = .tail W a c)) ∨
    (t = .return_ ∧ o = .ret stk₁ ∧ s' = s₁ ∧ f' = f₁) ∨
    (∃ l, t = .br l ∧ o = .br l.toNat stk₁ ∧ s' = s₁ ∧ f' = f₁) ∨
    (∃ (l : LabelIdx) (k : BitVec 32) (W : List Val), t = .brIf l ∧ stk₁ = W ++ [.i32 k] ∧
      ((k = 0 ∧ o = .normal W) ∨ (k ≠ 0 ∧ o = .br l.toNat W)) ∧ s' = s₁ ∧ f' = f₁) ∨
    (∃ (ws us us' : List Val) (X : List Admin), stk₁ = ws ++ us ∧ BrStep s₁ f₁ us t us' X ∧
      ((X = [] ∧ o = .normal (ws ++ us')) ∨
        ∃ l, X = [.plain (.br l)] ∧ o = .br l.toNat (ws ++ us')) ∧ s' = s₁ ∧ f' = f₁) := by
  have hterm := Proofs.MachineComplete.term_isTerminator hsg ht
  cases h with
  | val hv => exact absurd hv (by rw [Proofs.MachineComplete.term_val_none hsg ht]; simp)
  | simple hi h₁ h =>
    have := Proofs.MachineComplete.term_noncontrol hsg ht hi; subst this
    exact (Proofs.MachineComplete.steps_unreachable_not_vals h₁).elim
  | simpleTrap => exact .inl rfl
  | br => exact .inr (.inr (.inr (.inr (.inl ⟨_, rfl, rfl, rfl, rfl⟩))))
  | ret => exact .inr (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)))
  | @brIf _ _ _ _ ws k l _ _ h =>
    by_cases hk : k = 0
    · subst hk
      simp only [↓reduceIte, List.nil_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := runC_nil h
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨l, 0, ws, rfl, rfl, .inl ⟨rfl, rfl⟩, rfl, rfl⟩)))))
    · simp only [hk, ↓reduceIte, List.singleton_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.MachineComplete.run_br_inv h
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨l, k, ws, rfl, rfl, .inr ⟨hk, rfl⟩, rfl, rfl⟩)))))
  | @brData _ _ _ _ ws us us' _ X _ _ hb h =>
    rcases Proofs.MachineComplete.brStep_X hb with rfl | ⟨l, rfl⟩
    · simp only [List.nil_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := runC_nil h
      exact .inr (.inr (.inr (.inr (.inr (.inr ⟨ws, us, us', [], rfl, hb, .inl ⟨rfl, rfl⟩, rfl,
        rfl⟩)))))
    · simp only [List.singleton_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.MachineComplete.run_br_inv h
      exact .inr (.inr (.inr (.inr (.inr (.inr ⟨ws, us, us', _, rfl, hb, .inr ⟨l, rfl, rfl⟩, rfl,
        rfl⟩)))))
  | throw => exact .inr (.inl ⟨trivial, _, rfl⟩)
  | throwRefNull => exact .inl rfl
  | throwRefExn => exact .inr (.inl ⟨trivial, _, rfl⟩)
  | returnCall => exact .inr (.inr (.inl ⟨trivial, .inr ⟨_, _, _, rfl⟩⟩))
  | returnCallRef hc => exact .inr (.inr (.inl ⟨rcr_tail hc, .inr ⟨_, _, _, rfl⟩⟩))
  | returnCallRefNull hc => exact .inr (.inr (.inl ⟨rcr_tail hc, .inl ⟨_, _, rfl⟩⟩))
  | returnCallIndirect h =>
    rcases (Proofs.MachineComplete.run_rci (.returnCallIndirect h)).2 with rfl | hw | hw
    · exact .inl rfl
    · exact .inr (.inr (.inl ⟨trivial, .inr hw⟩))
    · exact .inr (.inr (.inl ⟨trivial, .inl hw⟩))
  | block => exact absurd ⟨_, _, _, _, StructKind.block⟩ hns
  | loop => exact absurd ⟨_, _, _, _, StructKind.loop⟩ hns
  | if_ => exact absurd ⟨_, _, _, _, StructKind.if_⟩ hns
  | tryTable => exact absurd ⟨_, _, _, _, StructKind.tryTable⟩ hns
  | _ => simp [isTerminator] at hterm

theorem flowRel_tailNull {fl : Flow} {W : List Val} {c : Admin}
    (h : Bridge.FlowRel fl (.tailNull W c)) : fl = .trap := by
  cases fl <;> simp_all [Bridge.FlowRel]

theorem not_flowRel_tail {fl : Flow} {W : List Val} {a : Nat} {c : Admin} :
    ¬ Bridge.FlowRel fl (.tail W a c) := by
  cases fl <;> simp [Bridge.FlowRel]

theorem dispL_flow {body : Expr} {b : BlockId} {ls : List LFrame}
    {r : Store H × Frame × Abstract.CallXP.POut} {st' : MState H} (h : DispL body b ls r st') :
    ∃ s f fl, r = (s, f, .flow fl) := by
  cases h <;> exact ⟨_, _, _, rfl⟩

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chkF_noTry chk_struct tryT_of_noTry
  arity_eq_blockArity entry_inv) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **A logged block step without a structured terminator projects to one `MStepC` step**
(exceptions on, every call form). -/
theorem proj_runE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {b : BlockId}
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
  have hnt := chkF_noTry hNT _ _ _ hF
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
  obtain ⟨-, hf', -, hgo⟩ := evalOXP_goodO hA d hg hoc'
  obtain ⟨s₂, f₂, fl, rfl⟩ := dispL_flow hd
  obtain ⟨s', f', o, hrun, hs', hf'', hfr⟩ :=
    MachineLProjE.flat_runP (P := P) (host := host) hA hflat d hg hoc'
  simp only at hf' hgo
  subst hs' hf''
  rw [List.reverse_reverse] at hrun
  have hf₂ : f₂.module = mi := by rw [hf', hf]
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
    · exact abrupt_proj hb hbody hbo (fun W h => hnorm ⟨W, h⟩) hfr hd hnt
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
        | raise =>
          exact ⟨_, .raise hb hterm hthr hbody hthen (fun k L hL hT => absurd hT (by
            rw [hnt L (List.mem_of_getElem? hL)]; simp)), .inl rfl⟩
        | catch_ _ hL hT => exact absurd hT (by rw [hnt _ (List.mem_of_getElem? hL)]; simp)
        | catchOut _ hL hT => exact absurd hT (by rw [hnt _ (List.mem_of_getElem? hL)]; simp)
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
      exact abrupt_proj hb hbody hbo (fun W h => by cases h) hfr hd hnt
    | throw a =>
      obtain ⟨rfl, rfl, rfl⟩ := hthen
      exact abrupt_proj hb hbody hbo (fun W h => by cases h) hfr hd hnt
    | _ => exact hbo.elim

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chkF_noTry chk_struct tryT_of_noTry
  arity_eq_blockArity entry_inv) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **A logged block step whose segment ends abruptly before a structured terminator**. -/
theorem proj_abortE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l : List (Abstract.SCall H)} {r : Store H × Frame × Abstract.CallXP.POut} {st' : MState H}
    (hb : lookup body b = some sg)
    (hr : Abstract.EvalLXPS s f stk.reverse (liftInstrs sg.body) l r) (hnn : ¬ r.2.2.IsNormal)
    (hd : DispL body b ls r st') (hl : ∀ e ∈ l, CloseOk C e) (hg : Γ.Good s)
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
  obtain ⟨s₂, f₂, fl, rfl⟩ := dispL_flow hd
  obtain ⟨s', f', o, hrun, hs', hf'', hfr⟩ := MachineLProjE.flat_runP (P := P) (host := host) hA
    hflat (Proofs.MachineLClosed.logged_closed hr hl) hg hoc'
  subst hs' hf''
  rw [List.reverse_reverse] at hrun
  have hbo := runC_body_out hbodyNT hrun
  refine abrupt_proj hb hrun hbo (fun W h => ?_) hfr hd (chkF_noTry hNT _ _ _ hF)
  subst h
  obtain ⟨ws, rfl, -⟩ := flowRel_normal hfr
  exact hnn trivial

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chkF_noTry chk_struct tryT_of_noTry
  arity_eq_blockArity entry_inv) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **Entering an arm** projects to `MStepC`'s `enter`. -/
theorem proj_enterE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C)
    {mi : ModuleInst} {nl ret : Nat} {body : Expr} (hNT : NoTry body) {b : BlockId} {sg : Segment}
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
  have hnt : tryT = false := tryT_of_noTry hNT hc hsg ht hkind
  simp only [liftInstrs, List.singleton_append, Interp.chkE, Option.bind_eq_some_iff] at hrest
  obtain ⟨o₂, h₂, hrest⟩ := hrest
  obtain ⟨np', nr', hba, hle, ho₂, oa, hoa, hoaE⟩ := chk_struct hkind hnt hsel harm h₂
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
    refine ⟨c, sg, i, c', np', nr', by simpa using hc, hsg, ht, harm, hkind, hba, rfl, hoaE,
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
/-- **A logged step projects to one `MStepC` step** (exceptions on, every call form, bodies
without `try_table`). -/
theorem proj_stepE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, MStepC P host C body st stC ∧ ProjRel st' stC := by
  cases hs with
  | run hb ht hr hd =>
    exact proj_runE hA hNT hb ht hr hd hl (by simpa [MInv] using hok) hg hn hI
  | abort hb hr hnn hd => exact proj_abortE hA hNT hb hr hnn hd hl hg hn hI
  | enter hb ht harm hkind hr hsel har hg' =>
    exact proj_enterE hA hNT hb ht harm hkind hr hsel har hg' hl hg hn hI

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged run projects to an `MStepC` run**, step by step (exceptions on, every call form,
bodies without `try_table`). -/
theorem proj_runLE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {st st' : MState H}
    {l : List (Abstract.SCall H)} (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) st stC ∧ ProjRel st' stC := by
  induction h with
  | refl => exact ⟨_, .refl, .inl rfl⟩
  | @step st st₁ st₂ l₁ l₂ hs hr ih =>
    have hl₁ : ∀ e ∈ l₁, CloseOk C e := fun e he => hl e (List.mem_append_left _ he)
    have hl₂ : ∀ e ∈ l₂, CloseOk C e := fun e he => hl e (List.mem_append_right _ he)
    obtain ⟨stC₁, hC₁, hR₁⟩ := proj_stepE (P := P) (host := host) hA hNT hs hl₁ hok hg hn hI
    obtain ⟨hg₁, hn₁, hI₁⟩ := MachineLProjI.cinv_step hA hNT hs hl₁ hok hg hn hI
    rcases hR₁ with rfl | hR₁
    · obtain ⟨stC₂, hC₂, hR₂⟩ := ih hl₂ (MachineLFwd.mstep_ok hs hok) hg₁ hn₁ hI₁
      exact ⟨stC₂, .head hC₁ hC₂, hR₂⟩
    · obtain ⟨rfl, -⟩ := mrunL_sink hr (fun b h => by rw [hR₁.1] at h; cases h)
      exact ⟨stC₁, .single hC₁, .inr hR₁⟩

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged run from the CFG entry projects to an `MStepC` run from the CFG entry** (exceptions
on, every call form, bodies without `try_table`), for a body passing the function's own check. -/
theorem proj_initialE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {ret : Nat}
    {body : Expr} (hNT : NoTry body) {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : Interp.endsAt (Interp.chkE (Interp.ehExt Γ.tags) Γ.funcs f.module f.locals.length ret
      [ret] (some 0) (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk C e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) (initial body s f) stC ∧ ProjRel st' stC :=
  proj_runLE hA hNT h hl (MachineLFwd.initial_ok body s f) hg rfl
    (MachineLProjI.cinv_initial (s := s) (f := f) rfl hchk)

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons) in
open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **An answered tail call projects to `MStepC.tail`**: a block whose straight-line code ends in
a pending tail call (`TailL`), answered by a `CloseOk C` entry, steps on `MStepC` (frame
replacement) to the sink the answer stands for (`tailSink`). -/
theorem proj_tailE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {st : MState H} {l : List (Abstract.SCall H)} {s₁ s₂ : Store H}
    {f₁ : Frame} {a n : Nat} {args : List Val} {b : (List Val ⊕ Nat) ⊕ PUnit.{1}}
    (ht : TailL body st l (s₁, f₁, .tail a args n)) (hl : ∀ e ∈ l, CloseOk C e)
    (he : CloseOk C (Abstract.SCall.mk a args s₁ b s₂)) (hg : Γ.Good st.store)
    (hn : st.frame.locals.length = nl) (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    MStepC P host C body st (tailSink b s₂ f₁) := by
  cases ht with
  | @tail bb sg stk ls s _ f _ _ _ _ _ hb hns hr =>
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf hg hn
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Binaryen.liftInstrs_append, chkE_append] at hchk
  obtain ⟨oc, hoc, -⟩ := Option.bind_eq_some_iff.mp hchk
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
      | some t => simp [htt] at hi; subst hi; exact liftInstr_of_not_struct (hns _ htt)
  obtain ⟨s', f', o, hrun, W, c', rfl, hc', rfl, rfl, fi, ps, rs, W₀, hfi, hty, rfl, hlen, rfl⟩ :=
    MachineLProjE.flat_runP (P := P) (host := host) hA hflat
      (Proofs.MachineLClosed.logged_closed hr hl) hg hoc'
  rw [List.reverse_reverse] at hrun
  rw [show expression (codeOf sg) = expression sg.body ++ expression sg.term.toList by
    simp [MachineL.codeOf, expression]] at hrun
  obtain ⟨s₃, f₃, o₁, hbody, hthen⟩ := Proofs.Region.run_split hrun rfl
  have hbo := runC_body_out hbodyNT hbody
  cases hterm : sg.term with
  | none =>
    simp only [hterm, Option.toList_none, expression, List.map_nil] at hthen
    obtain ⟨h1, -, -⟩ := thenC_nil hthen
    cases o₁ <;> simp_all [OutFlat]
  | some t =>
    simp only [hterm, Option.toList_some, expression, List.map_cons, List.map_nil] at hthen
    cases o₁ with
    | normal stk₁ =>
      change RunC P host C s₃ f₃ stk₁ [.plain t] s₁ f₁ (.tail (W₀ ++ args) a c') at hthen
      have htc : t.IsTailCall := by
        rcases term_runE hsg hterm (hns t hterm) hthen with
          h | ⟨-, _, h⟩ | ⟨htc, -⟩ | ⟨-, h, -⟩ | ⟨_, -, h, -⟩ | ⟨_, k, _, -, -, hk, -⟩ |
          ⟨_, _, _, _, -, -, hX, -⟩
        · cases h
        · cases h
        · exact htc
        · cases h
        · cases h
        · rcases hk with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
        · rcases hX with ⟨-, h⟩ | ⟨_, -, h⟩ <;> cases h
      obtain ⟨j, hj⟩ := MachineLProjC.brVals_junk ls.length ls (W₀ ++ args)
      have hargs : brVals ls.length ls (W₀ ++ args) = (j ++ W₀) ++ args := by
        rw [hj, List.append_assoc]
      rcases b with (ws | t') | u
      · obtain ⟨fi', ps', rs', fl, vs, hfi', hty', hcall, hvs, rfl⟩ := he
        rw [hfi] at hfi'; cases hfi'; rw [hty] at hty'; cases hty'
        have hend : tailEnd rs.length s₂ f₁ fl = some ⟨.exit, (vs.take rs.length).reverse, [], s₂, f₁⟩ := by
          cases fl <;> simp_all [tailEnd, Flow.retVals]
        exact .tail hb hterm htc hbody hthen hfi hty hargs hlen hcall hend
      · exact .tail hb hterm htc hbody hthen hfi hty hargs hlen he rfl
      · exact .tail hb hterm htc hbody hthen hfi hty hargs hlen he rfl
    | _ => first | exact hbo.elim | (obtain ⟨h1, -, -⟩ := hthen; cases h1)

theorem tailL_block {body : Expr} {st : MState H} {l : List (Abstract.SCall H)}
    {r : Store H × Frame × Abstract.CallXP.POut} (h : TailL body st l r) :
    ∃ b, st.node = .block b := by
  cases h; exact ⟨_, rfl⟩

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged run from the CFG entry ending in an answered tail call** is an `MStepC` run from
the CFG entry to the sink the answer stands for (exceptions on, every call form, bodies without
`try_table`), for a body passing the function's own check. -/
theorem proj_tail_initialE {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {ret : Nat}
    {body : Expr} (hNT : NoTry body) {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : Interp.endsAt (Interp.chkE (Interp.ehExt Γ.tags) Γ.funcs f.module f.locals.length ret
      [ret] (some 0) (liftInstrs body)) ret = true)
    {l l' : List (Abstract.SCall H)} {st : MState H} {s₁ s₂ : Store H} {f₁ : Frame} {a n : Nat}
    {args : List Val} {b : (List Val ⊕ Nat) ⊕ PUnit.{1}}
    (h : MRunL body (initial body s f) l st) (ht : TailL body st l' (s₁, f₁, .tail a args n))
    (hl : ∀ e ∈ l ++ l', CloseOk C e) (he : CloseOk C (Abstract.SCall.mk a args s₁ b s₂)) :
    Relation.ReflTransGen (MStepC P host C body) (initial body s f) (tailSink b s₂ f₁) := by
  have hl₁ : ∀ e ∈ l, CloseOk C e := fun e he => hl e (List.mem_append_left _ he)
  have hl₂ : ∀ e ∈ l', CloseOk C e := fun e he => hl e (List.mem_append_right _ he)
  have hok := MachineLFwd.initial_ok body s f
  have hI₀ := MachineLProjI.cinv_initial (s := s) (f := f) rfl hchk
  obtain ⟨stC, hC, hR⟩ := proj_runLE (P := P) (host := host) hA hNT h hl₁ hok hg rfl hI₀
  obtain ⟨hg', hn', hI'⟩ := MachineLProjI.cinv_run hA hNT h hl₁ hok hg rfl hI₀
  obtain ⟨bb, hbb⟩ := tailL_block ht
  rcases hR with rfl | hR
  · exact hC.tail (proj_tailE hA ht hl₂ he hg' hn' hI')
  · rw [hbb] at hR; cases hR.1

end Silmaril.Wasm.Cfg.Proofs.MachineLProjX
