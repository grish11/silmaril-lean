module

public import Silmaril.Proofs.Wasm.Cfg.BridgeBwdTree

@[expose] public section

/-!
# The backward bridge: pending tail calls (proofs)

A region run that ends in a pending tail call `Out.tail W a c` leaves the call to the frame; the
native evaluator makes it at once, with the oracle's answer on the top `ps.length` values. The
backward statement for that outcome (`BwdTL`) is therefore about **every** answer: for every
native result `r` that the oracle's answer gives (`ResOut … (.tail W a c) r`), the trees run
natively to `r`. Along the way, `TailOk`: the callee's parameters are on the stack `W`, so that a
label's outer values under `W` (`labelTail`) do not change the call's arguments
(`tail_shift`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Bridge

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (EvalOX TailRes tailPop tailFlow isXCall)
open Silmaril.Wasm.Abstract.CallXT (EvalOXT KeepsTy tailAnn)

set_option linter.unusedSimpArgs false

variable {H : Type} {C : Abstract.CallRel H}

/-- The callee's parameters are on the stack `W` of a pending tail call of `a`. -/
def TailOk (s : Store H) (a : Nat) (W : List Val) : Prop :=
  ∀ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi →
    Validation.DefType.funcType? fi.type = some (ps, rs) → ps.length ≤ W.length

theorem tailOk_append {s : Store H} {a : Nat} {W : List Val} (ws : List Val)
    (h : TailOk s a W) : TailOk s a (ws ++ W) :=
  fun fi ps rs h1 h2 => (h fi ps rs h1 h2).trans (by simp)

/-- **A label's outer values under a pending tail call do not change its arguments.** -/
theorem tail_shift {s' : Store H} {f' : Frame} {a : Nat} {c : Admin} {ws W : List Val}
    {r : Store H × Frame × Flow} (hok : TailOk s' a W)
    (hres : ResOut C s' f' (.tail (ws ++ W) a c) r) : ResOut C s' f' (.tail W a c) r := by
  obtain ⟨fi, ps, rs, W₀, args, fl, hfi, hty, hW, hn, hcall, hfl, h2, h3⟩ := hres
  have hle := hok fi ps rs hfi hty
  have h1 : args = (W.reverse.take ps.length).reverse := by
    have := congrArg (fun l => (l.reverse.take ps.length).reverse) hW
    simp only [List.reverse_append] at this
    rw [List.take_append_of_le_length (by simp; omega), List.take_left' (by simp [hn]),
      List.reverse_reverse] at this
    exact this.symm
  refine ⟨fi, ps, rs, (W.reverse.drop ps.length).reverse, args, fl, hfi, hty, ?_, hn, hcall,
    hfl, h2, h3⟩
  rw [h1, ← List.reverse_append, List.take_append_drop, List.reverse_reverse]

theorem tailFlow_escapes (n : Nat) (fl : Flow) : (tailFlow n fl).Escapes := by
  rcases fl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp [tailFlow, Flow.Escapes]

theorem tail_escapes {s' : Store H} {f' : Frame} {W : List Val} {a : Nat} {c : Admin}
    {r : Store H × Frame × Flow} (h : ResOut C s' f' (.tail W a c) r) : r.2.2.Escapes := by
  obtain ⟨-, -, rs, -, -, fl, -, -, -, -, -, -, -, h3⟩ := h
  rw [h3]; exact tailFlow_escapes _ _

theorem not_normal_of_escapes {fl : Flow} (h : fl.Escapes) : ¬ fl.IsNormal := by
  cases fl <;> simp_all [Flow.Escapes, Flow.IsNormal]

set_option linter.unusedTactic false in
/-- **Only a tail call ends a one-instruction region run in a pending tail call**, among the
instructions without bodies. -/
theorem tail_plain_inv {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {us W : List Val} {i : Instr} {a : Nat} {c : Admin} (hs : structuredInstr i = false)
    (h : RunC P host C s f us [.plain i] s' f' (.tail W a c)) :
    Bridge.isTailCall i = true := by
  generalize ho : (Region.Out.tail W a c) = o at h
  generalize hcode : [Admin.plain i] = code at h
  cases h with
  | val _ h' =>
    simp only [List.cons.injEq] at hcode; obtain ⟨-, rfl⟩ := hcode
    obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; cases ho
  | simple _ _ h' =>
    simp only [List.cons.injEq] at hcode; obtain ⟨-, rfl⟩ := hcode
    obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; cases ho
  | @brIf _ _ _ _ _ k _ _ _ h' =>
    simp only [List.cons.injEq] at hcode; obtain ⟨-, rfl⟩ := hcode
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, List.nil_append] at h'
      obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; cases ho
    · simp only [hk, ↓reduceIte, List.singleton_append] at h'
      obtain ⟨rfl, -, -⟩ := Proofs.Region.run_br_inv h'; cases ho
  | brData hb h' =>
    simp only [List.cons.injEq] at hcode; obtain ⟨-, rfl⟩ := hcode
    cases hb <;> simp only [List.nil_append, List.singleton_append, List.append_nil] at h' <;>
      first
        | (obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; cases ho)
        | (obtain ⟨rfl, -, -⟩ := Proofs.Region.run_br_inv h'; cases ho)
  | call _ _ _ _ _ h' =>
    simp only [List.cons.injEq] at hcode; obtain ⟨-, rfl⟩ := hcode
    obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; cases ho
  | callInd _ _ _ _ _ _ h' =>
    simp only [List.cons.injEq] at hcode; obtain ⟨-, rfl⟩ := hcode
    obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; cases ho
  | callRef _ _ _ _ _ h' =>
    simp only [List.cons.injEq] at hcode; obtain ⟨-, rfl⟩ := hcode
    obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; cases ho
  | returnCall =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode; obtain ⟨rfl, -⟩ := hcode; rfl
  | returnCallRef hc =>
    simp only [List.cons.injEq] at hcode; obtain ⟨rfl, -⟩ := hcode
    cases i <;> simp_all [Admin.IsReturnCallRef, Bridge.isTailCall]
  | returnCallIndirect =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode; obtain ⟨rfl, -⟩ := hcode; rfl
  | _ =>
    first
      | (cases ho; done)
      | (simp at hcode; done)
      | (simp only [List.cons.injEq, Admin.plain.injEq] at hcode
         obtain ⟨rfl, -⟩ := hcode
         simp [structuredInstr] at hs)

/-! ## Blocks ending in a pending tail call -/

section Blocks

variable {P : Profile} {host : HostSemantics H}

theorem labelExit_tail {ws : List Val} {oi : Region.Out} {W : List Val} {a : Nat} {c : Admin}
    (hx : LabelExit ws oi (.tail W a c)) : ∃ W', oi = .tail W' a c ∧ W = ws ++ W' := by
  rcases oi with _ | ⟨_ | _, _⟩ | _ | _ | _ | ⟨W', a', c'⟩ | _ <;> simp [LabelExit] at hx
  obtain ⟨rfl, rfl, rfl⟩ := hx
  exact ⟨_, rfl, rfl⟩

/-- **A block's label ending in a pending tail call**, backwards: its body does. -/
theorem label_tail {s s' : Store H} {f f' : Frame} {ws us W : List Val} {n : Nat}
    {B : List Instr} {a : Nat} {c : Admin} {Q : Store H × Frame × Flow → Prop}
    (ihT : ∀ {sB fB W' a' c'}, RunC P host C s f us (expression B) sB fB (.tail W' a' c') →
      TailOk sB a' W' ∧ ∀ r, ResOut C sB fB (.tail W' a' c') r → Q r)
    (h : RunC P host C s f ws [.label n [] (vals us ++ expression B)] s' f' (.tail W a c)) :
    TailOk s' a W ∧ ∀ r, ResOut C s' f' (.tail W a c) r → Q r := by
  rcases run_label_inv h with ⟨s₁, f₁, us', hin, hk⟩ | ⟨s₁, f₁, us₁, us₂, hin, hn, hk⟩ |
      ⟨oi, hin, hx⟩
  · obtain ⟨h1, -, -⟩ := Proofs.Region.run_nil_inv hk; cases h1
  · have hk' : RunC P host C s₁ f₁ (ws ++ us₂) [] s' f' (.tail W a c) :=
      Proofs.Region.run_vals_inv (code := []) (by simpa [expression] using hk)
    obtain ⟨h1, -, -⟩ := Proofs.Region.run_nil_inv hk'; cases h1
  · obtain ⟨W', rfl, rfl⟩ := labelExit_tail hx
    obtain ⟨hok, hall⟩ := ihT (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
    exact ⟨tailOk_append ws hok, fun r hr => hall r (tail_shift hok hr)⟩

/-- **A block ending in a pending tail call**, backwards: its body does, and the native body
run escapes the block. -/
theorem block_tail {s s' : Store H} {f f' : Frame} {stk : List Val} {bt : BlockType}
    {body : List BExpr} {np nr : Nat} {W : List Val} {a : Nat} {c : Admin}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (ihT : ∀ {sB fB W' a' c'}, RunC P host C s f (stk.take np).reverse
        (expression (BExpr.lowerList body)) sB fB (.tail W' a' c') →
      TailOk sB a' W' ∧ ∀ r, ResOut C sB fB (.tail W' a' c') r →
        EvalOX C s f (stk.take np) body r)
    (h : RunC P host C s f stk.reverse [.plain (.block bt (BExpr.lowerList body))] s' f'
      (.tail W a c)) :
    TailOk s' a W ∧ ∀ r, ResOut C s' f' (.tail W a c) r →
      EvalOX C s f (stk.take np) body r ∧ r.2.2.Escapes := by
  obtain ⟨t₁, t₂, hbt, rfl, rfl⟩ := blockType_of_arity har
  obtain ⟨ws, us, t₁', t₂', hW, hbt', hm, hl⟩ := run_block_inv h
  rw [hbt] at hbt'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hbt')
  rw [rev_split stk t₁.length] at hW
  obtain ⟨rfl, rfl⟩ := List.append_inj' hW (by rw [hm, len_rev_take hp])
  refine label_tail (Q := fun r => EvalOX C s f (stk.take t₁.length) body r ∧ r.2.2.Escapes)
    (fun hr => ?_) hl
  obtain ⟨hok, hall⟩ := ihT hr
  exact ⟨hok, fun r hres => ⟨hall r hres, tail_escapes hres⟩⟩

end Blocks

/-! ## Loops ending in a pending tail call -/

section Loops

variable {P : Profile} {host : HostSemantics H} {bt : BlockType} {body : List BExpr}
  {np nr : Nat}

set_option linter.unusedTactic false in
/-- The two code shapes of a loop's region run ending in a pending tail call: values then the
loop, and the loop's label. The tail call is made in the body, after any number of re-entries. -/
theorem loop_tail_aux {Inv : Store H → Frame → List Val → Prop} {T : Prop}
    (hI : ∀ {s f stk}, Inv s f stk → LoopStep P host C bt body np nr T Inv s f stk)
    (ihT : ∀ {s f stk}, Inv s f stk → ∀ {sB fB W' a' c'}, RunC P host C s f (stk.take np).reverse
        (expression (BExpr.lowerList body)) sB fB (.tail W' a' c') →
      TailOk sB a' W' ∧ ∀ r, ResOut C sB fB (.tail W' a' c') r →
        EvalOX C s f (stk.take np) body r)
    {s s' : Store H} {f f' : Frame} {W : List Val} {code : List Admin} {o : Region.Out}
    (h : RunC P host C s f W code s' f' o) :
    (∀ us stk Wt a c, code = vals us ++ [.plain (.loop bt (BExpr.lowerList body))] →
        W ++ us = stk.reverse → Inv s f stk → o = .tail Wt a c →
        TailOk s' a Wt ∧ ∀ r, ResOut C s' f' o r → EvalOX C s f stk [.loop bt body] r) ∧
      (∀ us stk Wt a c, code = [.label np [.loop bt (BExpr.lowerList body)]
          (vals us ++ expression (BExpr.lowerList body))] →
        W ++ us = stk.reverse → us.length = np → Inv s f stk → o = .tail Wt a c →
        TailOk s' a Wt ∧ ∀ r, ResOut C s' f' o r → EvalOX C s f stk [.loop bt body] r) := by
  induction h with
  | @val s s' f f' vs a v code o hv _ ih =>
    refine ⟨fun us stk Wt a c hc hW hinv ho => ?_, fun us stk Wt a c hc => by
      simp only [List.cons.injEq] at hc; obtain ⟨rfl, -⟩ := hc; simp [Admin.val?] at hv⟩
    rcases loop_code_cases hc.symm with ⟨rfl, rfl, rfl⟩ | ⟨u, us', rfl, rfl, rfl⟩
    · simp [Admin.val?] at hv
    · rw [Admin.val?_toAdmin, Option.some.injEq] at hv
      subst hv
      exact ih.1 us' stk Wt a c rfl (by simpa using hW) hinv ho
  | @loop s s' f f' ws us₀ bt' b t₁ t₂ code o hbt hm _ ih =>
    refine ⟨fun us stk Wt a c hc hW hinv ho => ?_, fun us stk Wt a c hc => by simp at hc⟩
    rcases loop_code_cases hc.symm with ⟨rfl, h1, rfl⟩ | ⟨u, us', rfl, h1, -⟩
    · simp only [Admin.plain.injEq, Instr.loop.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have hs := hI hinv
      obtain ⟨t₁', t₂', hbt', h1', -⟩ := blockType_of_arity hs.har
      rw [hbt] at hbt'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hbt')
      exact ih.2 us₀ stk Wt a c (by rw [h1']) (by simpa using hW) (hm.trans h1') hinv ho
    · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
  | labelNormal hin hk _ _ =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    obtain ⟨h1, -, -⟩ := Proofs.Region.run_nil_inv (by
      simp only [List.cons.injEq] at hc; obtain ⟨-, rfl⟩ := hc; exact hk)
    subst ho; cases h1
  | @labelBr0 s s₁ s' f f₁ f' vs us₁ us₂ n cont inner code o hin hn hk _ ihk =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    have hs := hI hinv
    rw [rev_split stk n] at hW
    obtain ⟨rfl, rfl⟩ := List.append_inj' hW (by rw [hlen, len_rev_take hs.hp])
    obtain ⟨rb, hrb, hres⟩ := hs.ihb (.inr (nt_br _ _))
      (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
    obtain ⟨vs, junk, rfl, hj⟩ := resOut_br_inv hres
    have hle := hs.hbr hrb
    obtain rfl := top_of_append hj hn hle
    obtain ⟨hok, hall⟩ := ihk.1 (vs.take n).reverse (vs.take n ++ stk.drop n) Wt a c
      (by simp [expression]) (by simp) (hs.back hrb) ho
    exact ⟨hok, fun r hr => .loopBack hs.har hrb (hall r hr)⟩
  | @labelTail s s₁ f f₁ vs us' n cont inner code a' c' hin =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    simp only [Region.Out.tail.injEq] at ho
    obtain ⟨rfl, rfl, rfl⟩ := ho
    have hs := hI hinv
    rw [rev_split stk n] at hW
    obtain ⟨rfl, rfl⟩ := List.append_inj' hW (by rw [hlen, len_rev_take hs.hp])
    obtain ⟨hok, hall⟩ := ihT hinv (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
    refine ⟨tailOk_append _ hok, fun r hr => ?_⟩
    have hr' := tail_shift hok hr
    obtain ⟨r1, r2, r3⟩ := r
    exact .loopEsc hs.har (hall _ hr') (tail_escapes hr')
  | labelBrSucc hin =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => by cases ho⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
  | labelRet hin =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => by cases ho⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
  | labelTrap hin =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => by cases ho⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
  | labelThrow hin =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => by cases ho⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
  | labelTailNull hin =>
    refine ⟨fun us stk Wt a c hc => ?_, fun us stk Wt a c hc hW hlen hinv ho => by cases ho⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
  | _ =>
    refine ⟨fun us stk Wt a c hc _ _ _ => ?_, fun us stk Wt a c hc _ _ _ _ => ?_⟩
    · first
        | (simp at hc; done)
        | (rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
           · first
               | (cases h1; done)
               | (cases h1; simp_all [SingleThreaded.Det.famOf, Admin.IsReturnCallRef]; done)
               | (cases h1; cases ‹BrStep _ _ _ _ _ _›; done)
           · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp only [Val.toAdmin] at h1 <;>
               first
                 | (cases h1; done)
                 | (cases h1; simp_all [SingleThreaded.Det.famOf, Admin.IsReturnCallRef]; done)
                 | (cases h1; cases ‹BrStep _ _ _ _ _ _›; done))
    · first
        | (simp at hc; done)
        | (simp only [List.cons.injEq] at hc; obtain ⟨rfl, -⟩ := hc
           simp_all [Admin.IsReturnCallRef, SingleThreaded.Det.famOf]; done)

end Loops

/-! ## The backward bridge for pending tail calls -/

section Main

variable {o : SingleThreaded.GrowOracle} {P₀ : Profile}

/-- The backward statement for a tree list ending in a pending tail call. -/
def BwdTL (o : SingleThreaded.GrowOracle) (C : Abstract.CallRel H) (es : List BExpr) : Prop :=
  ∀ {s s' : Store H} {f f' : Frame} {stk W : List Val} {a : Nat} {c : Admin},
    TypedT s f stk es →
    RunC (SingleThreaded.profile o) noHostX C s f stk.reverse (expression (BExpr.lowerList es))
      s' f' (.tail W a c) →
    TailOk s' a W ∧ ∀ r, ResOut C s' f' (.tail W a c) r → EvalOX C s f stk es r

/-- The backward statement for one tree ending in a pending tail call. -/
def Bwd1T (o : SingleThreaded.GrowOracle) (C : Abstract.CallRel H) (e : BExpr) : Prop :=
  ∀ {s s' : Store H} {f f' : Frame} {stk W : List Val} {a : Nat} {c : Admin} {es : List BExpr},
    TypedT s f stk (e :: es) →
    RunC (SingleThreaded.profile o) noHostX C s f stk.reverse (expression (BExpr.lower e))
      s' f' (.tail W a c) →
    TailOk s' a W ∧ ∀ r, ResOut C s' f' (.tail W a c) r → EvalOX C s f stk [e] r

theorem structured_of_flatChk {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h₀ : Nat} {i : Instr} {oc : Option Nat}
    (h : flatChkE tExt F mi nl ret labels h₀ i = some oc) : structuredInstr i = false := by
  cases i <;> simp_all [flatChkE, flatEff, structuredInstr, tExt]

variable (hC : OracleSoundT P₀ noHostX C) (hCk : KeepsTy C)
include hC hCk

/-- **The tail call at its site, natively**: the callee's parameters are on the stack, and every
oracle answer is the native `tail` rule's result. -/
theorem tail_site {i : Instr} {args es : List BExpr} {s sa : Store H} {f fa : Frame}
    {stk stk₁ : List Val} {a : Nat} {c : Admin} (ht : TypedT s f stk (.op i args :: es))
    (hra : EvalOX C s f stk args (sa, fa, .normal stk₁))
    (hres : TailRes sa fa i stk₁ (some (a, stk₁.drop (tailPop i)))) :
    TailOk sa a (stk₁.drop (tailPop i)).reverse ∧
      ∀ r, ResOut C sa fa (.tail (stk₁.drop (tailPop i)).reverse a c) r →
        EvalOX C s f stk [.op i args] r := by
  have hT := evalOXT_of_typedT hC hCk hra (args_typedT ht)
  obtain ⟨rest, hct, hTF, hTM, labels, ret, oc, hS, hfc⟩ := site_typedT hC hCk hT ht
  have ht0 := ht
  obtain ⟨_, labels', ret', out', hS', hc, -⟩ := ht0
  have key : ∀ (fi : FuncInst H) (ps rs : List Validation.CValType), sa.funcs[a]? = some fi →
      Validation.DefType.funcType? fi.type = some (ps, rs) →
      ps.length + tailPop i ≤ stk₁.length := fun fi ps rs hfi hty =>
    (tail_preT hS' (arityG hC hT) hres hfi hty (tailAnn_typed hres hct hfi hty hTF hTM hfc)
      hc).2.1
  refine ⟨fun fi ps rs hfi hty => ?_, fun r hr => ?_⟩
  · have := key fi ps rs hfi hty
    simp only [List.length_reverse, List.length_drop]; omega
  · obtain ⟨fi, ps, rs, W₀, args', fl, hfi, hty, hW, hn, hcall, hfl, h2, h3⟩ := hr
    have hp := key fi ps rs hfi hty
    have hargs : args' = ((stk₁.drop (tailPop i)).take ps.length).reverse := by
      rw [rev_split (stk₁.drop (tailPop i)) ps.length] at hW
      exact (List.append_inj' hW.symm (by
        rw [hn, len_rev_take (by simp only [List.length_drop]; omega)])).2
    obtain ⟨r1, r2, r3⟩ := r
    simp only at h2 h3
    subst h2 h3
    exact .tail hra hres hfi hty (by rw [← hargs]; exact hcall) hfl

/-- **Sequencing, backwards, to a pending tail call.** -/
theorem bwdT_cons {e : BExpr} {es : List BExpr} (h1 : Bwd1T o C e) (hl : BwdTL o C es) :
    BwdTL o C (e :: es) := by
  intro s s' f f' stk W a c ht h
  rw [show expression (BExpr.lowerList (e :: es)) =
      expression (BExpr.lower e) ++ expression (BExpr.lowerList es) by
    simp [BExpr.lowerList, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  by_cases hn : ∃ us, o₁ = .normal us
  · obtain ⟨us, rfl⟩ := hn
    obtain ⟨r₁, hr₁, hres₁⟩ := bwdL_all hC hCk [e] (typedT_head ht) (.inr (nt_normal _))
      (by simpa [BExpr.lowerList] using ha)
    obtain rfl := resOut_normal_inv hres₁
    simp only [ThenC] at hb
    have hT : EvalOXT C s f stk [e] _ := evalOXT_of_typedT hC hCk hr₁ (typedT_head ht)
    obtain ⟨hok, hall⟩ := hl (cont_typedT hC hCk hT ht) (by simpa using hb)
    exact ⟨hok, fun r hr => by simpa using evalOX_append hr₁ rfl (hall r hr)⟩
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    obtain ⟨hok, hall⟩ := h1 ht ha
    exact ⟨hok, fun r hr => by
      simpa using evalOX_stop (B := es) (hall r hr) (not_normal_of_escapes (tail_escapes hr))⟩

/-- **An operator tree to a pending tail call, backwards**: through its arguments, or at a tail
call (direct, by reference, or indirect with a callee). -/
theorem bwd1T_op {i : Instr} {args : List BExpr} (iha : BwdTL o C args) :
    Bwd1T o C (.op i args) := by
  intro s s' f f' stk W a c es ht h
  rw [show expression (BExpr.lower (.op i args)) =
      expression (BExpr.lowerList args) ++ [.plain i] by simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  by_cases hn : ∃ us, o₁ = .normal us
  swap
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    obtain ⟨hok, hall⟩ := iha (args_typedT ht) ha
    refine ⟨hok, fun r hr => ?_⟩
    obtain ⟨r1, r2, r3⟩ := r
    exact .argsAbort (hall _ hr) (not_normal_of_escapes (tail_escapes hr))
  obtain ⟨us, rfl⟩ := hn
  obtain ⟨⟨sa, fa, fla⟩, hra, hresa⟩ := bwdL_all hC hCk args (args_typedT ht) (.inr (nt_normal _)) ha
  have he := resOut_normal_inv hresa
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp only [ThenC] at hb
  have hT := evalOXT_of_typedT hC hCk hra (args_typedT ht)
  obtain ⟨_, _, _, _, _, _, _, _, hfc⟩ := site_typedT hC hCk hT ht
  clear hresa
  have hti := tail_plain_inv (structured_of_flatChk hfc) hb
  cases i with
  | returnCall x =>
    cases hb with
    | @returnCall _ _ _ x a' fi' _ hfi =>
      have := tail_site hC hCk (c := .returnCallRefType fi'.type) ht hra (.direct hfi)
      simpa [tailPop] using this
    | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
    | val hv => simp [Admin.val?] at hv
    | simple hi => simp [SingleThreaded.Det.famOf] at hi
    | brData hb => cases hb
  | returnCallRef y =>
    cases hb with
    | returnCallRef hc =>
      rw [show (W ++ [Val.ref (.func a)]).reverse = .ref (.func a) :: W.reverse by simp] at hra
      have := tail_site hC hCk (c := .plain (.returnCallRef y)) ht hra .ref
      simpa [tailPop] using this
    | val hv => simp [Admin.val?] at hv
    | simple hi => simp [SingleThreaded.Det.famOf] at hi
    | brData hb => cases hb
  | returnCallIndirect x y =>
    obtain ⟨W', a', i', rfl, rfl, rfl, ⟨-, hout⟩ | ⟨fa', c', hres, ho⟩⟩ := run_rci_cases hb
    · rcases hout with h' | ⟨_, h'⟩ <;> cases h'
    · simp only [Region.Out.tail.injEq] at ho
      obtain ⟨rfl, rfl, rfl⟩ := ho
      rw [show (W ++ [Val.num ⟨.int a'.intType, i'⟩]).reverse =
        .num ⟨.int a'.intType, i'⟩ :: W.reverse by simp] at hra
      have := tail_site hC hCk (c := c) ht hra (.indirect hres)
      simpa [tailPop] using this
  | _ => simp [Bridge.isTailCall] at hti

omit hC hCk in
/-- **A block tree to a pending tail call, backwards.** -/
theorem bwd1T_block {bt : BlockType} {body : List BExpr} (ihT : BwdTL o C body) :
    Bwd1T o C (.block bt body) := by
  intro s s' f f' stk W a c es ht h
  have ht0 := ht
  obtain ⟨rest, labels, ret, out', hS, hc, -, -, -⟩ := ht0
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := by rw [arity_eq]; exact ha
  obtain ⟨hp, -, -⟩ := arity_block_pre har hc
  have htb := block_body_typedT (P := SingleThreaded.profile o) har ht
  obtain ⟨hok, hall⟩ := block_tail har hp (fun hr => ihT htb hr)
    (by simpa [BExpr.lower, expression] using h)
  refine ⟨hok, fun r hr => ?_⟩
  obtain ⟨hb, he⟩ := hall r hr
  obtain ⟨r1, r2, r3⟩ := r
  exact .blockEsc har hb he

/-- **A loop tree to a pending tail call, backwards**, through every re-entry. -/
theorem bwd1T_loop {bt : BlockType} {body : List BExpr} (ihb : BwdL o C body)
    (ihT : BwdTL o C body) : Bwd1T o C (.loop bt body) := by
  intro s s' f f' stk W a c es ht h
  have ht0 := ht
  obtain ⟨rest, labels, ret, out', hS, hc, -, -, -⟩ := ht0
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := by rw [arity_eq]; exact ha
  have hI : ∀ {s f stk}, LoopInv bt body np nr s f stk →
      LoopStep (SingleThreaded.profile o) noHostX C bt body np nr (tailFreeL body = true)
        (LoopInv bt body np nr) s f stk := fun hinv => loopStep_of hC hCk ihb hinv
  have hT : ∀ {s f stk}, LoopInv bt body np nr s f stk → ∀ {sB fB W' a' c'},
      RunC (SingleThreaded.profile o) noHostX C s f (stk.take np).reverse
        (expression (BExpr.lowerList body)) sB fB (.tail W' a' c') →
      TailOk sB a' W' ∧ ∀ r, ResOut C sB fB (.tail W' a' c') r →
        EvalOX C s f (stk.take np) body r := by
    intro s f stk hinv sB fB W' a' c' hr
    exact ihT (loop_body_typedT (P := P₀) hinv.2 hinv.1) hr
  exact (loop_tail_aux hI hT h).1 [] stk W a c (by simp [BExpr.lower, expression, vals])
    (by simp) ⟨typedT_head ht, har⟩ rfl

/-- **A conditional tree to a pending tail call, backwards.** -/
theorem bwd1T_if {bt : BlockType} {c t el : List BExpr} (ihc : BwdTL o C c)
    (iht : BwdTL o C t) (ihe : BwdTL o C el) : Bwd1T o C (.if_ bt c t el) := by
  intro s s' f f' stk W a c₀ es ht h
  rw [show expression (BExpr.lower (.if_ bt c t el)) = expression (BExpr.lowerList c) ++
      [.plain (.if_ bt (BExpr.lowerList t) (BExpr.lowerList el))] by
    simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  by_cases hn : ∃ us, o₁ = .normal us
  swap
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    obtain ⟨hok, hall⟩ := ihc (cond_typedT ht) ha
    refine ⟨hok, fun r hr => ?_⟩
    obtain ⟨r1, r2, r3⟩ := r
    exact .ifAbort (hall _ hr) (not_normal_of_escapes (tail_escapes hr))
  obtain ⟨us, rfl⟩ := hn
  obtain ⟨⟨sa, fa, fla⟩, hrc, hresc⟩ :=
    bwdL_all hC hCk c (cond_typedT ht) (.inr (nt_normal _)) ha
  have he := resOut_normal_inv hresc
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp only [ThenC] at hb
  obtain ⟨ws, k, rfl, hblk⟩ := run_if_inv hb
  have hrev : (ws ++ [Val.i32 k]).reverse = Val.i32 k :: ws.reverse := by simp
  rw [hrev] at hrc
  have hT := evalOXT_of_typedT hC hCk hrc (cond_typedT ht)
  have ht0 := ht
  obtain ⟨rest, labels, ret, out', hS, hc, hct, -, -⟩ := ht0
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hcc, hk⟩ := chk1_ifE h1
  have hct' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (BExpr.lowerList c) ++
      (.plain (.if_ bt (BExpr.lowerList t) (BExpr.lowerList el)) ::
        (expression (BExpr.lowerList es) ++ rest))⟩ := by
    simpa [BExpr.lowerList, BExpr.lower, expression, List.append_assoc] using hct
  obtain ⟨-, hoc, inv⟩ := prefix_typedT hC hT hS hcc hct'
  obtain ⟨np, nr, hba, hp1, -⟩ := hk _ hoc
  have har₁ : Binaryen.arity fa bt = some (np, nr) := by rw [arity_eq, inv.2.1]; exact hba
  have hb' : truthy (Val.i32 k) = some (k != 0) := by
    simp [truthy, asInt, Val.i32]; exact ⟨k, rfl, rfl⟩
  have hta := arm_typedT hC hCk hT hb' har₁ ht
  have hp : np ≤ ws.reverse.length := by simp at hp1 ⊢; omega
  have iharm : BwdTL o C (if (k != 0) = true then t else el) := by split <;> assumption
  have hlow : BExpr.lowerList (if (k != 0) = true then t else el) =
      if k = 0 then BExpr.lowerList el else BExpr.lowerList t := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp [hk0]
      split <;> simp_all
  obtain ⟨hok, hall⟩ := block_tail har₁ hp (fun hr => iharm hta hr)
    (by rw [hlow, List.reverse_reverse]; exact hblk)
  refine ⟨hok, fun r hr => ?_⟩
  obtain ⟨harm, hesc⟩ := hall r hr
  obtain ⟨r1, r2, r3⟩ := r
  exact .ifEsc hrc hb' har₁ harm hesc

omit hC hCk in
theorem bwd1T_tryTable {bt : BlockType} {cs : List Catch} {body : List BExpr} :
    Bwd1T o C (.tryTable bt cs body) := by
  intro s s' f f' stk W a c es ht h
  obtain ⟨rest, labels, ret, out', hS, hc, -, -, -⟩ := ht
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hc
  simp [chk1E, tExt] at h1

omit hC hCk in
theorem bwdTL_nil : BwdTL o C [] := by
  intro s s' f f' stk W a c ht h
  obtain ⟨h1, -, -⟩ :=
    Proofs.Region.run_nil_inv (by simpa [BExpr.lowerList, expression] using h)
  cases h1

/-- **The tree-level backward bridge for a pending tail call**, by induction on the size of the
trees (loops by induction on their region run, `loop_tail_aux`). -/
theorem bwdTL_all : ∀ es, BwdTL o C es := by
  intro es
  induction hn : sizeOf es using Nat.strong_induction_on generalizing es with
  | _ n ih =>
  cases es with
  | nil => exact bwdTL_nil
  | cons e es =>
    have hs : sizeOf (e :: es) = 1 + sizeOf e + sizeOf es := rfl
    have ihe : ∀ es', sizeOf es' < sizeOf e → BwdTL o C es' := fun es' hl =>
      ih (sizeOf es') (by omega) es' rfl
    have ihr : BwdTL o C es := ih (sizeOf es) (by omega) es rfl
    have h1 : Bwd1T o C e := by
      cases e with
      | op i args => exact bwd1T_op hC hCk (ihe args (by simp))
      | block bt body => exact bwd1T_block (ihe body (by simp))
      | loop bt body => exact bwd1T_loop hC hCk (bwdL_all hC hCk body) (ihe body (by simp))
      | if_ bt c t el =>
        exact bwd1T_if hC hCk (ihe c (by simp; omega)) (ihe t (by simp; omega))
          (ihe el (by simp))
      | tryTable bt cs body => exact bwd1T_tryTable
    intro s s' f f' stk W a c
    exact bwdT_cons hC hCk h1 ihr

end Main

end Silmaril.Wasm.Cfg.Proofs.Bridge
