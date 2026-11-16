module

public import Silmaril.Proofs.Wasm.Cfg.BridgeBwd
public import Silmaril.Wasm.Cfg.BridgeBwd.Defs
public import Silmaril.Proofs.Wasm.Cfg.BridgeBwdRci

@[expose] public section

/-!
# The backward bridge: trees (proofs)

Sequencing of native runs (`evalOX_append`, `evalOX_stop`), used to put the per-tree backward
cases together along a tree list.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Bridge

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (EvalOX)

set_option linter.unusedSimpArgs false

variable {H : Type} {C : Abstract.CallRel H}

/-! ## Sequencing native runs -/

theorem evalOX_nil_inv {s : Store H} {f : Frame} {stk : List Val} {r : Store H × Frame × Flow}
    (h : EvalOX C s f stk [] r) : r = (s, f, .normal stk) := by
  cases h; rfl

/-- **A native run that falls through continues with the next trees.** -/
theorem evalOX_append {s : Store H} {f : Frame} {stk : List Val} {A B : List BExpr}
    {r₀ r : Store H × Frame × Flow} (h : EvalOX C s f stk A r₀) :
    ∀ {s₁ f₁ stk₁}, r₀ = (s₁, f₁, .normal stk₁) → EvalOX C s₁ f₁ stk₁ B r →
      EvalOX C s f stk (A ++ B) r := by
  induction h with
  | nil => intro _ _ _ he hB; cases he; exact hB
  | argsAbort _ hfl => intro _ _ _ he; cases he; simp [Flow.IsNormal] at hfl
  | callOk hargs hfi hty hcall hvs _ _ ihk =>
    intro _ _ _ he hB; exact .callOk hargs hfi hty hcall hvs (ihk he hB)
  | callTrap => intro _ _ _ he; cases he
  | callThrow => intro _ _ _ he; cases he
  | opOk hi hargs hflat _ _ ihk => intro _ _ _ he hB; exact .opOk hi hargs hflat (ihk he hB)
  | opStop _ _ _ hfl => intro _ _ _ he; cases he; simp [Flow.IsNormal] at hfl
  | blockOk har hbody hvs _ _ ihk => intro _ _ _ he hB; exact .blockOk har hbody hvs (ihk he hB)
  | blockBrk => intro _ _ _ he; cases he
  | blockEsc _ _ hfl => intro _ _ _ he; cases he; simp [Flow.Escapes] at hfl
  | loopOk har hbody _ _ ihk => intro _ _ _ he hB; exact .loopOk har hbody (ihk he hB)
  | loopBack har hbody _ _ ihk => intro _ _ _ he hB; exact .loopBack har hbody (ihk he hB)
  | loopBrk => intro _ _ _ he; cases he
  | loopEsc _ _ hfl => intro _ _ _ he; cases he; simp [Flow.Escapes] at hfl
  | ifOk hc hb har harm hvs _ _ _ ihk =>
    intro _ _ _ he hB; exact .ifOk hc hb har harm hvs (ihk he hB)
  | ifBrk => intro _ _ _ he; cases he
  | ifEsc _ _ _ _ hfl => intro _ _ _ he; cases he; simp [Flow.Escapes] at hfl
  | ifAbort _ hfl => intro _ _ _ he; cases he; simp [Flow.IsNormal] at hfl
  | callIndOk hargs hres hfi hty hcall hvs _ _ ihk =>
    intro _ _ _ he hB; exact .callIndOk hargs hres hfi hty hcall hvs (ihk he hB)
  | callIndRes => intro _ _ _ he; cases he
  | callIndStop _ _ _ _ _ hfl => intro _ _ _ he; cases he; simp [Flow.Abrupt] at hfl
  | callRefOk hargs hfi hty hcall hvs _ _ ihk =>
    intro _ _ _ he hB; exact .callRefOk hargs hfi hty hcall hvs (ihk he hB)
  | callRefNull => intro _ _ _ he; cases he
  | callRefStop _ _ _ _ hfl => intro _ _ _ he; cases he; simp [Flow.Abrupt] at hfl
  | tail =>
    intro _ _ _ he; simp only [Prod.mk.injEq] at he
    exact absurd he.2.2 (tailFlow_ne_normal _ _ _)
  | tailRes => intro _ _ _ he; cases he

/-- **A native run that does not fall through ends every longer tree list alike.** -/
theorem evalOX_stop {s : Store H} {f : Frame} {stk : List Val} {A B : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX C s f stk A r) (hn : ¬ r.2.2.IsNormal) :
    EvalOX C s f stk (A ++ B) r := by
  induction h with
  | nil => simp [Flow.IsNormal] at hn
  | argsAbort hargs hfl => exact .argsAbort hargs hfl
  | callOk hargs hfi hty hcall hvs _ _ ihk => exact .callOk hargs hfi hty hcall hvs (ihk hn)
  | callTrap hargs hfi hty hcall => exact .callTrap hargs hfi hty hcall
  | callThrow hargs hfi hty hcall => exact .callThrow hargs hfi hty hcall
  | opOk hi hargs hflat _ _ ihk => exact .opOk hi hargs hflat (ihk hn)
  | opStop hi hargs hflat hfl => exact .opStop hi hargs hflat hfl
  | blockOk har hbody hvs _ _ ihk => exact .blockOk har hbody hvs (ihk hn)
  | blockBrk har hbody => exact .blockBrk har hbody
  | blockEsc har hbody hfl => exact .blockEsc har hbody hfl
  | loopOk har hbody _ _ ihk => exact .loopOk har hbody (ihk hn)
  | loopBack har hbody _ _ ihk => exact .loopBack har hbody (ihk hn)
  | loopBrk har hbody => exact .loopBrk har hbody
  | loopEsc har hbody hfl => exact .loopEsc har hbody hfl
  | ifOk hc hb har harm hvs _ _ _ ihk => exact .ifOk hc hb har harm hvs (ihk hn)
  | ifBrk hc hb har harm => exact .ifBrk hc hb har harm
  | ifEsc hc hb har harm hfl => exact .ifEsc hc hb har harm hfl
  | ifAbort hc hfl => exact .ifAbort hc hfl
  | callIndOk hargs hres hfi hty hcall hvs _ _ ihk =>
    exact .callIndOk hargs hres hfi hty hcall hvs (ihk hn)
  | callIndRes hargs hres => exact .callIndRes hargs hres
  | callIndStop hargs hres hfi hty hcall hfl => exact .callIndStop hargs hres hfi hty hcall hfl
  | callRefOk hargs hfi hty hcall hvs _ _ ihk => exact .callRefOk hargs hfi hty hcall hvs (ihk hn)
  | callRefNull hargs => exact .callRefNull hargs
  | callRefStop hargs hfi hty hcall hfl => exact .callRefStop hargs hfi hty hcall hfl
  | tail hargs hres hfi hty hcall hfl => exact .tail hargs hres hfi hty hcall hfl
  | tailRes hargs hres => exact .tailRes hargs hres

/-! ## Inverting region runs of structured code -/

section Inv

variable {P : Profile} {host : HostSemantics H}



theorem run_block_inv {s s' : Store H} {f f' : Frame} {W : List Val} {bt : BlockType}
    {B : List Instr} {code : List Admin} {o : Region.Out}
    (h : RunC P host C s f W (.plain (.block bt B) :: code) s' f' o) :
    ∃ ws us t₁ t₂, W = ws ++ us ∧ f.module.blockType? bt = some (t₁, t₂) ∧
      us.length = t₁.length ∧
      RunC P host C s f ws (.label t₂.length [] (vals us ++ expression B) :: code) s' f' o := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | block hbt hm h => exact ⟨_, _, _, _, rfl, hbt, hm, h⟩

theorem run_loop_inv {s s' : Store H} {f f' : Frame} {W : List Val} {bt : BlockType}
    {B : List Instr} {code : List Admin} {o : Region.Out}
    (h : RunC P host C s f W (.plain (.loop bt B) :: code) s' f' o) :
    ∃ ws us t₁ t₂, W = ws ++ us ∧ f.module.blockType? bt = some (t₁, t₂) ∧
      us.length = t₁.length ∧
      RunC P host C s f ws (.label t₁.length [.loop bt B] (vals us ++ expression B) :: code)
        s' f' o := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | loop hbt hm h => exact ⟨_, _, _, _, rfl, hbt, hm, h⟩

theorem run_if_inv {s s' : Store H} {f f' : Frame} {W : List Val} {bt : BlockType}
    {T E : List Instr} {code : List Admin} {o : Region.Out}
    (h : RunC P host C s f W (.plain (.if_ bt T E) :: code) s' f' o) :
    ∃ ws k, W = ws ++ [.i32 k] ∧
      RunC P host C s f ws (.plain (.block bt (if k = 0 then E else T)) :: code) s' f' o := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | if_ h => exact ⟨_, _, rfl, h⟩

/-- How a region outcome leaves a label other than by falling through or branching to it. -/
def LabelExit (ws : List Val) : Region.Out → Region.Out → Prop
  | .br (l + 1) us, o => o = .br l (ws ++ us)
  | .ret us, o => o = .ret (ws ++ us)
  | .trap, o => o = .trap
  | .throw a, o => o = .throw a
  | .tail us a c, o => o = .tail (ws ++ us) a c
  | .tailNull us c, o => o = .tailNull (ws ++ us) c
  | _, _ => False

theorem run_label_inv {s s' : Store H} {f f' : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {inner code : List Admin} {o : Region.Out}
    (h : RunC P host C s f ws (.label n cont inner :: code) s' f' o) :
    (∃ s₁ f₁ us, RunC P host C s f [] inner s₁ f₁ (.normal us) ∧
        RunC P host C s₁ f₁ (ws ++ us) code s' f' o) ∨
      (∃ s₁ f₁ us₁ us₂, RunC P host C s f [] inner s₁ f₁ (.br 0 (us₁ ++ us₂)) ∧
        us₂.length = n ∧ RunC P host C s₁ f₁ ws (vals us₂ ++ expression cont ++ code) s' f' o) ∨
      (∃ oi, RunC P host C s f [] inner s' f' oi ∧ LabelExit ws oi o) := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | labelNormal hin h => exact .inl ⟨_, _, _, hin, h⟩
  | labelBr0 hin hn h => exact .inr (.inl ⟨_, _, _, _, hin, hn, h⟩)
  | labelBrSucc hin => exact .inr (.inr ⟨_, hin, rfl⟩)
  | labelRet hin => exact .inr (.inr ⟨_, hin, rfl⟩)
  | labelTrap hin => exact .inr (.inr ⟨_, hin, rfl⟩)
  | labelThrow hin => exact .inr (.inr ⟨_, hin, rfl⟩)
  | labelTail hin => exact .inr (.inr ⟨_, hin, rfl⟩)
  | labelTailNull hin => exact .inr (.inr ⟨_, hin, rfl⟩)

end Inv

/-- **Leaving a label abruptly, backwards**: the native flow of the body loses a label (a deeper
branch) or escapes unchanged, and ends as the label's outcome. -/
theorem labelExit_res {s' : Store H} {f' : Frame} {ws : List Val} {oi o : Region.Out}
    {r : Store H × Frame × Flow} (hres : ResOut C s' f' oi r) (hx : LabelExit ws oi o) :
    ∃ fl', ((∃ k vs, r.2.2 = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (r.2.2.Escapes ∧ fl' = r.2.2)) ∧
      ResOut C s' f' o (r.1, r.2.1, fl') := by
  obtain ⟨s₁, f₁, fl⟩ := r
  rcases oi with us | ⟨_ | l, us⟩ | us | _ | a | ⟨us, a, c⟩ | ⟨us, c⟩ <;>
    simp only [LabelExit] at hx <;> subst hx
  · obtain ⟨rfl, rfl, h⟩ := hres
    cases fl <;> simp only [FlowRel] at h
    obtain ⟨rfl, junk, rfl⟩ := h
    exact ⟨_, .inl ⟨_, _, rfl, rfl⟩, rfl, rfl, rfl, ws ++ junk, by simp⟩
  · obtain ⟨rfl, rfl, h⟩ := hres
    cases fl <;> simp only [FlowRel] at h
    obtain ⟨junk, rfl⟩ := h
    exact ⟨_, .inr ⟨by simp [Flow.Escapes], rfl⟩, rfl, rfl, ws ++ junk, by simp⟩
  · obtain ⟨rfl, rfl, h⟩ := hres
    cases fl <;> simp only [FlowRel] at h
    exact ⟨_, .inr ⟨by simp [Flow.Escapes], rfl⟩, rfl, rfl, trivial⟩
  · obtain ⟨rfl, rfl, h⟩ := hres
    cases fl <;> simp only [FlowRel] at h
    subst h
    exact ⟨_, .inr ⟨by simp [Flow.Escapes], rfl⟩, rfl, rfl, rfl⟩
  · obtain ⟨fi, ps, rs, W₀, args, fl₀, hfi, hty, rfl, hn, hcall, hfl₀, rfl, rfl⟩ := hres
    refine ⟨_, .inr ⟨?_, rfl⟩, fi, ps, rs, ws ++ W₀, args, fl₀, hfi, hty, by simp, hn, hcall,
      hfl₀, rfl, rfl⟩
    rcases fl₀ with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp [Abstract.CallX.tailFlow, Flow.Escapes]
  · obtain ⟨rfl, rfl, h⟩ := hres
    cases fl <;> simp only [FlowRel] at h
    exact ⟨_, .inr ⟨by simp [Flow.Escapes], rfl⟩, rfl, rfl, trivial⟩

theorem resOut_normal_inv {s' : Store H} {f' : Frame} {us : List Val} {r : Store H × Frame × Flow}
    (h : ResOut C s' f' (.normal us) r) : r = (s', f', .normal us.reverse) := by
  obtain ⟨s₁, f₁, fl⟩ := r
  obtain ⟨rfl, rfl, h⟩ := h
  cases fl <;> simp only [FlowRel] at h
  subst h; simp

theorem resOut_br_inv {s' : Store H} {f' : Frame} {l : Nat} {us : List Val}
    {r : Store H × Frame × Flow} (h : ResOut C s' f' (.br l us) r) :
    ∃ vs junk, r = (s', f', .brk l vs) ∧ us = junk ++ vs.reverse := by
  obtain ⟨s₁, f₁, fl⟩ := r
  obtain ⟨rfl, rfl, h⟩ := h
  cases fl <;> simp only [FlowRel] at h
  obtain ⟨rfl, junk, rfl⟩ := h
  exact ⟨_, junk, rfl, rfl⟩

/-- A region outcome other than a pending tail call of a function. -/
def NT (o : Region.Out) : Prop := ∀ W a c, o ≠ .tail W a c

theorem nt_normal (us : List Val) : NT (.normal us) := by intro W a c h; cases h

theorem nt_br (l : Nat) (us : List Val) : NT (.br l us) := by intro W a c h; cases h

theorem labelExit_nt {ws : List Val} {oi o : Region.Out} (hx : LabelExit ws oi o) (h : NT o) :
    NT oi := by
  rintro W a c rfl
  simp only [LabelExit] at hx
  exact h _ _ _ hx

/-- The top `n` values under junk, read top first. -/
theorem top_of_append {us₁ us₂ junk vs : List Val} {n : Nat} (h : us₁ ++ us₂ = junk ++ vs.reverse)
    (hn : us₂.length = n) (hle : n ≤ vs.length) : us₂ = (vs.take n).reverse := by
  rw [rev_split vs n, ← List.append_assoc] at h
  exact (List.append_inj' h (by rw [hn, len_rev_take hle])).2

/-! ## Blocks, backwards -/

/-- **How a block ends, natively**: its body's flow `fl` hands values to the continuation, loses a
label, or escapes; in each case the result is related to the region's outcome `o`. -/
def BlockEnd (C : Abstract.CallRel H) (s' : Store H) (f' : Frame) (o : Region.Out)
    (s₁ : Store H) (f₁ : Frame) (fl : Flow) (nr : Nat) (rest : List Val) : Prop :=
  (∃ vs, fl.blockVals = some vs ∧ ResOut C s' f' o (s₁, f₁, .normal (vs.take nr ++ rest))) ∨
    (∃ k vs, fl = .brk (k + 1) vs ∧ ResOut C s' f' o (s₁, f₁, .brk k vs)) ∨
    (fl.Escapes ∧ ResOut C s' f' o (s₁, f₁, fl))

section Blocks

variable {P : Profile} {host : HostSemantics H}

/-- **A region run of a block, backwards**, from the backward runs of its body and the body's
arity facts. -/
theorem block_bwd {s s' : Store H} {f f' : Frame} {stk : List Val} {bt : BlockType}
    {body : List BExpr} {np nr : Nat} {o : Region.Out} {T : Prop} (hT : T ∨ NT o)
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (ihb : ∀ {sB fB oB}, T ∨ NT oB → RunC P host C s f (stk.take np).reverse
        (expression (BExpr.lowerList body)) sB fB oB →
      ∃ rb, EvalOX C s f (stk.take np) body rb ∧ ResOut C sB fB oB rb)
    (hlen : ∀ {s₁ f₁ vs}, EvalOX C s f (stk.take np) body (s₁, f₁, .normal vs) → vs.length = nr)
    (hbr : ∀ {s₁ f₁ vs}, EvalOX C s f (stk.take np) body (s₁, f₁, .brk 0 vs) → nr ≤ vs.length)
    (h : RunC P host C s f stk.reverse [.plain (.block bt (BExpr.lowerList body))] s' f' o) :
    ∃ s₁ f₁ fl, EvalOX C s f (stk.take np) body (s₁, f₁, fl) ∧
      BlockEnd C s' f' o s₁ f₁ fl nr (stk.drop np) := by
  obtain ⟨t₁, t₂, hbt, rfl, rfl⟩ := blockType_of_arity har
  obtain ⟨ws, us, t₁', t₂', hW, hbt', hm, hl⟩ := run_block_inv h
  rw [hbt] at hbt'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hbt')
  rw [rev_split stk t₁.length] at hW
  obtain ⟨rfl, rfl⟩ := List.append_inj' hW (by rw [hm, len_rev_take hp])
  rcases run_label_inv hl with ⟨s₁, f₁, us', hin, hk⟩ | ⟨s₁, f₁, us₁, us₂, hin, hn, hk⟩ |
      ⟨oi, hin, hx⟩
  · obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv hk
    obtain ⟨rb, hrb, hres⟩ := ihb (.inr (nt_normal _))
      (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
    obtain rfl := resOut_normal_inv hres
    have hl' := hlen hrb
    refine ⟨_, _, _, hrb, .inl ⟨_, rfl, rfl, rfl, ?_⟩⟩
    simp only [FlowRel, List.reverse_append, List.reverse_reverse]
    rw [List.take_of_length_le (le_of_eq hl'), List.reverse_reverse]
  · obtain ⟨rb, hrb, hres⟩ := ihb (.inr (nt_br _ _))
      (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
    obtain ⟨vs, junk, rfl, hj⟩ := resOut_br_inv hres
    have hle := hbr hrb
    obtain rfl := top_of_append hj hn hle
    have hk' : RunC P host C s₁ f₁ ((stk.drop t₁.length).reverse ++ (vs.take t₂.length).reverse) []
        s' f' o := Proofs.Region.run_vals_inv (code := []) (by simpa [expression] using hk)
    obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv hk'
    exact ⟨_, _, _, hrb, .inl ⟨vs, rfl, rfl, rfl, by simp [FlowRel]⟩⟩
  · obtain ⟨rb, hrb, hres⟩ := ihb (hT.imp id (labelExit_nt hx))
      (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
    obtain ⟨fl', hfl, hres'⟩ := labelExit_res hres hx
    obtain ⟨s₁, f₁, fl⟩ := rb
    rcases hfl with ⟨k, vs, h1, rfl⟩ | ⟨hesc, rfl⟩
    · exact ⟨_, _, _, hrb, .inr (.inl ⟨k, vs, h1, hres'⟩)⟩
    · exact ⟨_, _, _, hrb, .inr (.inr ⟨hesc, hres'⟩)⟩

/-- A block's native ends, as a native run of the block. -/
theorem evalOX_block {s s' s₁ : Store H} {f f' f₁ : Frame} {stk : List Val} {bt : BlockType}
    {body : List BExpr} {np nr : Nat} {o : Region.Out} {fl : Flow}
    (har : Binaryen.arity f bt = some (np, nr))
    (hb : EvalOX C s f (stk.take np) body (s₁, f₁, fl))
    (he : BlockEnd C s' f' o s₁ f₁ fl nr (stk.drop np)) :
    ∃ r, EvalOX C s f stk [.block bt body] r ∧ ResOut C s' f' o r := by
  rcases he with ⟨vs, hvs, hres⟩ | ⟨k, vs, rfl, hres⟩ | ⟨hesc, hres⟩
  · exact ⟨_, .blockOk har hb hvs .nil, hres⟩
  · exact ⟨_, .blockBrk har hb, hres⟩
  · exact ⟨_, .blockEsc har hb hesc, hres⟩

end Blocks

/-! ## Loops, backwards -/

theorem loop_code_cases {us : List Val} {L : Admin} {a : Admin} {rest : List Admin}
    (h : vals us ++ [L] = a :: rest) :
    (us = [] ∧ a = L ∧ rest = []) ∨
      ∃ u us', us = u :: us' ∧ a = u.toAdmin ∧ rest = vals us' ++ [L] := by
  rcases us with _ | ⟨u, us'⟩
  · simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at h
    exact .inl ⟨rfl, h.1.symm, h.2.symm⟩
  · simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    exact .inr ⟨u, us', rfl, h.1.symm, h.2.symm⟩

section Loops

variable {P : Profile} {host : HostSemantics H} {bt : BlockType} {body : List BExpr}
  {np nr : Nat}

/-- What a loop's backward case needs at each entry `(s, f, stk)`: the block type's arity, enough
operands, the backward runs of the body, its arity facts, and the same at re-entry. -/
structure LoopStep (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H)
    (bt : BlockType) (body : List BExpr) (np nr : Nat) (T : Prop)
    (Inv : Store H → Frame → List Val → Prop) (s : Store H) (f : Frame) (stk : List Val) :
    Prop where
  har : Binaryen.arity f bt = some (np, nr)
  hp : np ≤ stk.length
  ihb : ∀ {sB fB oB}, T ∨ NT oB →
      RunC P host C s f (stk.take np).reverse (expression (BExpr.lowerList body))
      sB fB oB → ∃ rb, EvalOX C s f (stk.take np) body rb ∧ ResOut C sB fB oB rb
  hlen : ∀ {s₁ f₁ vs}, EvalOX C s f (stk.take np) body (s₁, f₁, .normal vs) → vs.length = nr
  hbr : ∀ {s₁ f₁ vs}, EvalOX C s f (stk.take np) body (s₁, f₁, .brk 0 vs) → np ≤ vs.length
  back : ∀ {s₁ f₁ vs}, EvalOX C s f (stk.take np) body (s₁, f₁, .brk 0 vs) →
      Inv s₁ f₁ (vs.take np ++ stk.drop np)


/-- A loop's label left other than by falling through or branching back. -/
theorem loop_exit {Inv : Store H → Frame → List Val → Prop} {s s₁ : Store H} {f f₁ : Frame}
    {stk W us : List Val} {oi o : Region.Out} {T : Prop}
    (hs : LoopStep P host C bt body np nr T Inv s f stk) (hT : T ∨ NT o)
    (hW : W ++ us = stk.reverse) (hlen : us.length = np)
    (hin : RunC P host C s f [] (vals us ++ expression (BExpr.lowerList body)) s₁ f₁ oi)
    (hx : LabelExit W oi o) :
    ∃ r, EvalOX C s f stk [.loop bt body] r ∧ ResOut C s₁ f₁ o r := by
  rw [rev_split stk np] at hW
  obtain ⟨rfl, rfl⟩ := List.append_inj' hW (by rw [hlen, len_rev_take hs.hp])
  obtain ⟨rb, hrb, hres⟩ := hs.ihb (hT.imp id (labelExit_nt hx)) (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
  obtain ⟨fl', hfl, hres'⟩ := labelExit_res hres hx
  obtain ⟨sb, fb, fl⟩ := rb
  rcases hfl with ⟨k, vs, h1, rfl⟩ | ⟨hesc, rfl⟩
  · simp only at h1; subst h1
    exact ⟨_, .loopBrk hs.har hrb, hres'⟩
  · exact ⟨_, .loopEsc hs.har hrb hesc, hres'⟩

set_option linter.unusedTactic false in
/-- The two code shapes a loop's region run passes through: values then the loop, and the
loop's label. -/
theorem loop_aux {Inv : Store H → Frame → List Val → Prop} {T : Prop}
    (hI : ∀ {s f stk}, Inv s f stk → LoopStep P host C bt body np nr T Inv s f stk)
    {s s' : Store H} {f f' : Frame} {W : List Val} {code : List Admin} {o : Region.Out}
    (h : RunC P host C s f W code s' f' o) :
    (∀ us stk, code = vals us ++ [.plain (.loop bt (BExpr.lowerList body))] →
        W ++ us = stk.reverse → Inv s f stk → (T ∨ NT o) →
        ∃ r, EvalOX C s f stk [.loop bt body] r ∧ ResOut C s' f' o r) ∧
      (∀ us stk, code = [.label np [.loop bt (BExpr.lowerList body)]
          (vals us ++ expression (BExpr.lowerList body))] →
        W ++ us = stk.reverse → us.length = np → Inv s f stk → (T ∨ NT o) →
        ∃ r, EvalOX C s f stk [.loop bt body] r ∧ ResOut C s' f' o r) := by
  induction h with
  | @val s s' f f' vs a v code o hv _ ih =>
    refine ⟨fun us stk hc hW hinv hT => ?_, fun us stk hc => by
      simp only [List.cons.injEq] at hc; obtain ⟨rfl, -⟩ := hc; simp [Admin.val?] at hv⟩
    rcases loop_code_cases hc.symm with ⟨rfl, rfl, rfl⟩ | ⟨u, us', rfl, rfl, rfl⟩
    · simp [Admin.val?] at hv
    · rw [Admin.val?_toAdmin, Option.some.injEq] at hv
      subst hv
      exact ih.1 us' stk rfl (by simpa using hW) hinv hT
  | @loop s s' f f' ws us₀ bt' b t₁ t₂ code o hbt hm _ ih =>
    refine ⟨fun us stk hc hW hinv hT => ?_, fun us stk hc => by simp at hc⟩
    rcases loop_code_cases hc.symm with ⟨rfl, h1, rfl⟩ | ⟨u, us', rfl, h1, -⟩
    · simp only [Admin.plain.injEq, Instr.loop.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have hs := hI hinv
      obtain ⟨t₁', t₂', hbt', h1', -⟩ := blockType_of_arity hs.har
      rw [hbt] at hbt'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hbt')
      exact ih.2 us₀ stk (by rw [h1']) (by simpa using hW) (hm.trans h1') hinv hT
    · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
  | @labelNormal s s₁ s' f f₁ f' vs us' n cont inner code o hin hk _ _ =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    have hs := hI hinv
    rw [rev_split stk n] at hW
    obtain ⟨rfl, rfl⟩ := List.append_inj' hW (by rw [hlen, len_rev_take hs.hp])
    obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv hk
    obtain ⟨rb, hrb, hres⟩ := hs.ihb (.inr (nt_normal _))
      (by simpa using Proofs.Region.run_vals_inv (vs := []) hin)
    obtain rfl := resOut_normal_inv hres
    have hl' := hs.hlen hrb
    refine ⟨_, .loopOk hs.har hrb .nil, rfl, rfl, ?_⟩
    simp only [FlowRel, List.reverse_append, List.reverse_reverse]
    rw [List.take_of_length_le (le_of_eq hl'), List.reverse_reverse]
  | @labelBr0 s s₁ s' f f₁ f' vs us₁ us₂ n cont inner code o hin hn hk _ ihk =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
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
    obtain ⟨r, hr, hres'⟩ := ihk.1 (vs.take n).reverse (vs.take n ++ stk.drop n) (by simp [expression])
      (by simp) (hs.back hrb) hT
    exact ⟨r, .loopBack hs.har hrb hr, hres'⟩
  | labelBrSucc hin =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    exact loop_exit (hI hinv) hT hW hlen hin rfl
  | labelRet hin =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    exact loop_exit (hI hinv) hT hW hlen hin rfl
  | labelTrap hin =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    exact loop_exit (hI hinv) hT hW hlen hin rfl
  | labelThrow hin =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    exact loop_exit (hI hinv) hT hW hlen hin rfl
  | labelTail hin =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    exact loop_exit (hI hinv) hT hW hlen hin rfl
  | labelTailNull hin =>
    refine ⟨fun us stk hc => ?_, fun us stk hc hW hlen hinv hT => ?_⟩
    · rcases loop_code_cases hc.symm with ⟨-, h1, -⟩ | ⟨u, -, -, h1, -⟩
      · cases h1
      · rcases u with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h1
    simp only [List.cons.injEq, Admin.label.injEq] at hc
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    exact loop_exit (hI hinv) hT hW hlen hin rfl
  | _ =>
    refine ⟨fun us stk hc _ _ _ => ?_, fun us stk hc _ _ _ _ => ?_⟩
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


theorem run_call_inv {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {W : List Val} {x : FuncIdx} {code : List Admin} {o : Region.Out}
    (h : RunC P host C s f W (.plain (.call x) :: code) s' f' o) :
    (∃ ws us a fi ps rs s₂ fl vs, W = ws ++ us ∧ s.func? f x = some (a, fi) ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧ us.length = ps.length ∧
        C s a us (s₂, fl) ∧ fl.retVals = some vs ∧
        RunC P host C s₂ f (ws ++ (vs.take rs.length).reverse) code s' f' o) ∨
      (∃ ws us a fi ps rs, W = ws ++ us ∧ s.func? f x = some (a, fi) ∧
        Validation.DefType.funcType? (FuncInst.type fi) = some (ps, rs) ∧ us.length = ps.length ∧
        C s a us (s', .trap) ∧ f' = f ∧ o = .trap) ∨
      (∃ ws us a fi ps rs t, W = ws ++ us ∧ s.func? f x = some (a, fi) ∧
        Validation.DefType.funcType? (FuncInst.type fi) = some (ps, rs) ∧ us.length = ps.length ∧
        C s a us (s', .throw t) ∧ f' = f ∧ o = .throw t) := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | call hfi hty hn hcall hvs h => exact .inl ⟨_, _, _, _, _, _, _, _, _, rfl, hfi, hty, hn, hcall, hvs, h⟩
  | callTrap hfi hty hn hcall => exact .inr (.inl ⟨_, _, _, _, _, _, rfl, hfi, hty, hn, hcall, rfl, rfl⟩)
  | callThrow hfi hty hn hcall =>
    exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl, hfi, hty, hn, hcall, rfl, rfl⟩)

theorem take_rev_append {ws us : List Val} {n : Nat} (h : us.length = n) :
    ((ws ++ us).reverse.take n).reverse = us ∧ (ws ++ us).reverse.drop n = ws.reverse := by
  rw [List.reverse_append]
  exact ⟨by rw [List.take_left' (by simp [h])]; simp, List.drop_left' (by simp [h])⟩


open Silmaril.Wasm.Abstract.CallX (isXCall xFree xFreeL) in
mutual

theorem tailFree_of_xFree : ∀ e : BExpr, xFree e = true → tailFree e = true
  | .op i args, h => by
    simp only [xFree, tailFree, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    exact ⟨by cases i <;> simp_all [isXCall, isTailCall], tailFreeL_of_xFreeL args h.2⟩
  | .block _ b, h => tailFreeL_of_xFreeL b h
  | .loop _ b, h => tailFreeL_of_xFreeL b h
  | .if_ _ c t e, h => by
    simp only [xFree, tailFree, Bool.and_eq_true] at h ⊢
    exact ⟨⟨tailFreeL_of_xFreeL c h.1.1, tailFreeL_of_xFreeL t h.1.2⟩, tailFreeL_of_xFreeL e h.2⟩
  | .tryTable _ _ b, h => tailFreeL_of_xFreeL b h

theorem tailFreeL_of_xFreeL : ∀ es : List BExpr, xFreeL es = true → tailFreeL es = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [xFreeL, tailFreeL, Bool.and_eq_true] at h ⊢
    exact ⟨tailFree_of_xFree e h.1, tailFreeL_of_xFreeL es h.2⟩

end

/-! ## The tree-level backward bridge, without tail calls -/

section Main

open Silmaril.Wasm.Abstract.CallXT (EvalOXT KeepsTy)
open Silmaril.Wasm.Abstract.CallX (isXCall)

variable {o : SingleThreaded.GrowOracle} {P₀ : Profile}

/-- The backward statement for a tree list. -/
def BwdL (o : SingleThreaded.GrowOracle) (C : Abstract.CallRel H) (es : List BExpr) : Prop :=
  ∀ {s s' : Store H} {f f' : Frame} {stk : List Val} {out : Region.Out}, TypedT s f stk es →
    (tailFreeL es = true ∨ NT out) →
    RunC (SingleThreaded.profile o) noHostX C s f stk.reverse (expression (BExpr.lowerList es))
      s' f' out →
    ∃ r, EvalOX C s f stk es r ∧ ResOut C s' f' out r

/-- The backward statement for one tree, at the head of a typed list. -/
def Bwd1 (o : SingleThreaded.GrowOracle) (C : Abstract.CallRel H) (e : BExpr) : Prop :=
  ∀ {s s' : Store H} {f f' : Frame} {stk : List Val} {out : Region.Out} {es : List BExpr},
    TypedT s f stk (e :: es) → (tailFree e = true ∨ NT out) →
    RunC (SingleThreaded.profile o) noHostX C s f stk.reverse (expression (BExpr.lower e))
      s' f' out →
    ∃ r, EvalOX C s f stk [e] r ∧ ResOut C s' f' out r

theorem typedT_head {s : Store H} {f : Frame} {stk : List Val} {e : BExpr} {es : List BExpr}
    (ht : TypedT s f stk (e :: es)) : TypedT s f stk [e] := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  refine ⟨expression (BExpr.lowerList es) ++ rest, labels, ret, o, hS,
    chk_consE.mpr ⟨o, h1, chkE_nil_selfT o⟩, ?_, hTF, hTM⟩
  rw [code_consX] at hct
  exact hct

theorem flowRel_not_tail {fl : Flow} {o : Region.Out} (h : FlowRel fl o) :
    ∀ W a c, o ≠ .tail W a c := by
  rintro W a c rfl; cases fl <;> simp [FlowRel] at h

theorem flatChk_of_tExt {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h₀ : Nat} {i : Instr} {oc : Option Nat} (hx : isXCall i = false)
    (h : flatChkE tExt F mi nl ret labels h₀ i = some oc) :
    flatChk F mi nl ret labels h₀ i = some oc := by
  cases i <;> simp_all [isXCall, flatChk, flatChkE, tExt, noExt]

theorem thenC_stop_inv {P : Profile} {host : HostSemantics H} {s₁ s' : Store H} {f₁ f' : Frame}
    {o₁ out : Region.Out} {B : List Admin} (hn : ∀ us, o₁ ≠ .normal us)
    (h : ThenC P host C s₁ f₁ o₁ B s' f' out) : out = o₁ ∧ s' = s₁ ∧ f' = f₁ := by
  cases o₁ with
  | normal us => exact absurd rfl (hn us)
  | _ => exact h

theorem nt_of_then {P : Profile} {host : HostSemantics H} {s₁ s' : Store H} {f₁ f' : Frame}
    {o₁ out : Region.Out} {B : List Admin} (hnt : NT out)
    (h : ThenC P host C s₁ f₁ o₁ B s' f' out) : NT o₁ := by
  rintro W a c rfl
  exact hnt W a c (thenC_stop_inv (fun us h => by cases h) h).1

theorem not_normal_of_res {s' : Store H} {f' : Frame} {o₁ : Region.Out}
    {r : Store H × Frame × Flow} (hres : ResOut C s' f' o₁ r) (hn : ∀ us, o₁ ≠ .normal us) :
    ¬ r.2.2.IsNormal := by
  obtain ⟨s₁, f₁, fl⟩ := r
  intro hN
  rcases fl with vs | _ | _ | _ | _ <;> simp only [Flow.IsNormal] at hN
  exact hn _ (resOut_normal hres).1

variable (hC : OracleSoundT P₀ noHostX C) (hCk : KeepsTy C)
include hC hCk

/-- **Sequencing, backwards.** -/
theorem bwd_cons {e : BExpr} {es : List BExpr} (h1 : Bwd1 o C e) (hl : BwdL o C es) :
    BwdL o C (e :: es) := by
  intro s s' f f' stk out ht hx h
  rw [show expression (BExpr.lowerList (e :: es)) =
      expression (BExpr.lower e) ++ expression (BExpr.lowerList es) by
    simp [BExpr.lowerList, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  have hx1 : tailFree e = true ∨ NT o₁ :=
    hx.imp (fun h => by simp only [tailFreeL, Bool.and_eq_true] at h; exact h.1) (nt_of_then · hb)
  have hx2 : tailFreeL es = true ∨ NT out :=
    hx.imp (fun h => by simp only [tailFreeL, Bool.and_eq_true] at h; exact h.2) id
  obtain ⟨r₁, hr₁, hres₁⟩ := h1 ht hx1 ha
  by_cases hn : ∃ us, o₁ = .normal us
  · obtain ⟨us, rfl⟩ := hn
    obtain rfl := resOut_normal_inv hres₁
    simp only [ThenC] at hb
    have hT : EvalOXT C s f stk [e] _ := evalOXT_of_typedT hC hCk hr₁ (typedT_head ht)
    obtain ⟨r, hr, hres⟩ := hl (cont_typedT hC hCk hT ht) hx2 (by simpa using hb)
    exact ⟨r, by simpa using evalOX_append hr₁ rfl hr, hres⟩
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    exact ⟨r₁, by simpa using evalOX_stop (B := es) hr₁ (not_normal_of_res hres₁ hn), hres₁⟩

/-- **A flat operator tree, backwards.** -/
theorem bwd1_op_flat {i : Instr} {args : List BExpr} (hi : ∀ x, i ≠ .call x)
    (hxi : isXCall i = false) (iha : BwdL o C args) : Bwd1 o C (.op i args) := by
  intro s s' f f' stk out es ht hx h
  rw [show expression (BExpr.lower (.op i args)) =
      expression (BExpr.lowerList args) ++ [.plain i] by simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  have hxa : tailFreeL args = true ∨ NT o₁ :=
    hx.imp (fun h => by simp only [tailFree, Bool.and_eq_true] at h; exact h.2) (nt_of_then · hb)
  obtain ⟨⟨sa, fa, fla⟩, hra, hresa⟩ := iha (args_typedT ht) hxa ha
  by_cases hn : ∃ us, o₁ = .normal us
  · obtain ⟨us, rfl⟩ := hn
    have he := resOut_normal_inv hresa
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [ThenC] at hb
    have hT := evalOXT_of_typedT hC hCk hra (args_typedT ht)
    obtain ⟨rest, hct, -, -, labels, ret, oc, -, hfc⟩ := site_typedT hC hCk hT ht
    have hct' : Sim.ContextTyped ⟨sa, fa, vals us.reverse.reverse ++ [.plain i]⟩ :=
      Sim.ContextTyped.suffix (rest := rest) (by rw [List.append_assoc]; exact hct)
    obtain ⟨fl, hev, hrel⟩ := flat_bwd hi (flatChk_of_tExt hxi hfc) hct' (by simpa using hb)
    by_cases hN : fl.IsNormal
    · rcases fl with stk₂ | _ | _ | _ | _ <;> simp only [Flow.IsNormal] at hN
      exact ⟨_, .opOk hi hra hev .nil, resOut_of_rel (flowRel_not_tail hrel) hrel⟩
    · exact ⟨_, .opStop hi hra hev hN, resOut_of_rel (flowRel_not_tail hrel) hrel⟩
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    exact ⟨_, .argsAbort hra (not_normal_of_res hresa hn), hresa⟩

omit hC hCk in
/-- **A direct call tree, backwards**: the region's call is answered by the same oracle entry. -/
theorem bwd1_call {x : FuncIdx} {args : List BExpr} (iha : BwdL o C args) :
    Bwd1 o C (.op (.call x) args) := by
  intro s s' f f' stk out es ht hx h
  rw [show expression (BExpr.lower (.op (.call x) args)) =
      expression (BExpr.lowerList args) ++ [.plain (.call x)] by
    simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  have hxa : tailFreeL args = true ∨ NT o₁ :=
    hx.imp (fun h => by simp only [tailFree, Bool.and_eq_true] at h; exact h.2) (nt_of_then · hb)
  obtain ⟨⟨sa, fa, fla⟩, hra, hresa⟩ := iha (args_typedT ht) hxa ha
  by_cases hn : ∃ us, o₁ = .normal us
  · obtain ⟨us, rfl⟩ := hn
    have he := resOut_normal_inv hresa
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [ThenC] at hb
    rcases run_call_inv hb with
      ⟨ws, us', a, fi, ps, rs, s₂, fl, vs, rfl, hfi, hty, hn', hcall, hvs, hk⟩ |
      ⟨ws, us', a, fi, ps, rs, rfl, hfi, hty, hn', hcall, rfl, rfl⟩ |
      ⟨ws, us', a, fi, ps, rs, t, rfl, hfi, hty, hn', hcall, rfl, rfl⟩
    · obtain ⟨htk, hdr⟩ := take_rev_append (ws := ws) hn'
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv hk
      refine ⟨_, .callOk hra hfi hty (by rw [htk]; exact hcall) hvs .nil, rfl, rfl, ?_⟩
      rw [hdr]; simp [FlowRel]
    · obtain ⟨htk, -⟩ := take_rev_append (ws := ws) hn'
      exact ⟨_, .callTrap hra hfi hty (by rw [htk]; exact hcall), rfl, rfl, trivial⟩
    · obtain ⟨htk, -⟩ := take_rev_append (ws := ws) hn'
      exact ⟨_, .callThrow hra hfi hty (by rw [htk]; exact hcall), rfl, rfl, rfl⟩
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    exact ⟨_, .argsAbort hra (not_normal_of_res hresa hn), hresa⟩

/-- **A block tree, backwards.** -/
theorem bwd1_block {bt : BlockType} {body : List BExpr} (ihb : BwdL o C body) :
    Bwd1 o C (.block bt body) := by
  intro s s' f f' stk out es ht hx h
  have hxb : tailFreeL body = true ∨ NT out := hx.imp (fun h => by simpa [tailFree] using h) id
  have ht0 := ht
  obtain ⟨rest, labels, ret, out', hS, hc, -, -, -⟩ := ht0
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := by rw [arity_eq]; exact ha
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  have htb := block_body_typedT (P := P₀) har ht
  obtain ⟨s₁, f₁, fl, hrb, he⟩ := block_bwd hxb har hp (fun hT hr => ihb htb hT hr)
    (fun hrun => by
      obtain ⟨ob, hob, -, hok, -⟩ := body_facts hS
        (arityG hC (evalOXT_of_typedT hC hCk hrun htb)) hb (take_length_of_le hp)
      exact length_of_ends hok hob)
    (fun hrun => by
      obtain ⟨ob, hob, -, hok, -⟩ := body_facts hS
        (arityG hC (evalOXT_of_typedT hC hCk hrun htb)) hb (take_length_of_le hp)
      exact blockVals_length hok hob rfl)
    (by simpa [BExpr.lower, expression] using h)
  exact evalOX_block har hrb he

/-- The loop invariant of a typed loop: typed at each entry, at the loop's arity. -/
def LoopInv (bt : BlockType) (body : List BExpr) (np nr : Nat) (s : Store H) (f : Frame)
    (stk : List Val) : Prop :=
  TypedT s f stk [.loop bt body] ∧ Binaryen.arity f bt = some (np, nr)

/-- **A typed loop's entries satisfy what the loop's backward case needs.** -/
theorem loopStep_of {bt : BlockType} {body : List BExpr} {np nr : Nat} (ihb : BwdL o C body) :
    ∀ {s f stk}, LoopInv bt body np nr s f stk →
      LoopStep (SingleThreaded.profile o) noHostX C bt body np nr (tailFreeL body = true)
        (LoopInv bt body np nr) s f stk := by
  rintro s f stk ⟨ht1, har⟩
  have ht2 := ht1
  obtain ⟨rest, labels, ret, out', hS, hc, -, -, -⟩ := ht2
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  have htb := loop_body_typedT (P := P₀) har ht1
  refine ⟨har, hp, fun hT hr => ihb htb hT hr, fun hrun => ?_, fun hrun => ?_, fun hrun => ?_⟩
  · obtain ⟨ob, hob, -, hok, -⟩ := body_facts hS
      (arityG hC (evalOXT_of_typedT hC hCk hrun htb)) hb (take_length_of_le hp)
    exact length_of_ends hok hob
  · obtain ⟨ob, hob, -, hok, -⟩ := body_facts hS
      (arityG hC (evalOXT_of_typedT hC hCk hrun htb)) hb (take_length_of_le hp)
    obtain ⟨m, hm, hle⟩ := hok
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle
  · have hT := evalOXT_of_typedT hC hCk hrun htb
    obtain ⟨-, -, -, -, inv⟩ := body_facts hS (arityG hC hT) hb (take_length_of_le hp)
    refine ⟨loop_back_typedT hC hCk har hT ht1, ?_⟩
    rw [arity_eq, inv.2.1, ← arity_eq]; exact har

/-- **A loop tree, backwards**, through every re-entry. -/
theorem bwd1_loop {bt : BlockType} {body : List BExpr} (ihb : BwdL o C body) :
    Bwd1 o C (.loop bt body) := by
  intro s s' f f' stk out es ht hx h
  have hxb : tailFreeL body = true ∨ NT out := hx.imp (fun h => by simpa [tailFree] using h) id
  have ht0 := ht
  obtain ⟨rest, labels, ret, out', hS, hc, -, -, -⟩ := ht0
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, -⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := by rw [arity_eq]; exact ha
  have hI : ∀ {s f stk}, LoopInv bt body np nr s f stk →
      LoopStep (SingleThreaded.profile o) noHostX C bt body np nr (tailFreeL body = true)
        (LoopInv bt body np nr) s f stk := fun hinv => loopStep_of hC hCk ihb hinv
  exact (loop_aux hI h).1 [] stk (by simp [BExpr.lower, expression, vals]) (by simp)
    ⟨typedT_head ht, har⟩ hxb

/-- **A conditional tree, backwards**: the condition, then the chosen arm as a block. -/
theorem bwd1_if {bt : BlockType} {c t el : List BExpr} (ihc : BwdL o C c) (iht : BwdL o C t)
    (ihe : BwdL o C el) : Bwd1 o C (.if_ bt c t el) := by
  intro s s' f f' stk out es ht hx h
  rw [show expression (BExpr.lower (.if_ bt c t el)) = expression (BExpr.lowerList c) ++
      [.plain (.if_ bt (BExpr.lowerList t) (BExpr.lowerList el))] by
    simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  have hxc : tailFreeL c = true ∨ NT o₁ := hx.imp (fun h => by
    simp only [tailFree, Bool.and_eq_true] at h; exact h.1.1) (nt_of_then · hb)
  obtain ⟨⟨sa, fa, fla⟩, hrc, hresc⟩ := ihc (cond_typedT ht) hxc ha
  by_cases hn : ∃ us, o₁ = .normal us
  · obtain ⟨us, rfl⟩ := hn
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
    have iharm : BwdL o C (if (k != 0) = true then t else el) := by split <;> assumption
    have hxa : tailFreeL (if (k != 0) = true then t else el) = true ∨ NT out := hx.imp (fun h => by
      simp only [tailFree, Bool.and_eq_true] at h; split <;> simp_all) id
    have hlow : BExpr.lowerList (if (k != 0) = true then t else el) =
        if k = 0 then BExpr.lowerList el else BExpr.lowerList t := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · simp [hk0]
        split <;> simp_all
    have hfacts := fun {s₂ f₂ fl}
        (hrun : EvalOX C sa fa (ws.reverse.take np) (if (k != 0) = true then t else el)
          (s₂, f₂, fl)) =>
      if_facts hS (arityG hC hT) har₁ (arityG hC (evalOXT_of_typedT hC hCk hrun hta)) hc
    obtain ⟨s₂, f₂, fl, harm, he⟩ := block_bwd hxa har₁ hp (fun hT hr => iharm hta hT hr)
      (fun hrun => by
        obtain ⟨-, ob, -, -, hob, hok, -⟩ := hfacts hrun; exact length_of_ends hok hob)
      (fun hrun => by
        obtain ⟨-, ob, -, -, hob, hok, -⟩ := hfacts hrun; exact blockVals_length hok hob rfl)
      (by rw [hlow, List.reverse_reverse]; exact hblk)
    rcases he with ⟨vs, hvs, hres⟩ | ⟨k', vs, rfl, hres⟩ | ⟨hesc, hres⟩
    · exact ⟨_, .ifOk hrc hb' har₁ harm hvs .nil, hres⟩
    · exact ⟨_, .ifBrk hrc hb' har₁ harm, hres⟩
    · exact ⟨_, .ifEsc hrc hb' har₁ harm hesc, hres⟩
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    exact ⟨_, .ifAbort hrc (not_normal_of_res hresc hn), hresc⟩


omit hC hCk in
/-- **An indirect call tree, backwards**: the region resolves the callee as the native evaluator
does (`CallRes.IndRes`), and the call is answered by the same oracle entry. -/
theorem bwd1_callInd {x : TableIdx} {y : TypeIdx} {args : List BExpr} (iha : BwdL o C args) :
    Bwd1 o C (.op (.callIndirect x y) args) := by
  intro s s' f f' stk out es ht hx h
  rw [show expression (BExpr.lower (.op (.callIndirect x y) args)) =
      expression (BExpr.lowerList args) ++ [.plain (.callIndirect x y)] by
    simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  have hxa : tailFreeL args = true ∨ NT o₁ :=
    hx.imp (fun h => by simp only [tailFree, Bool.and_eq_true] at h; exact h.2) (nt_of_then · hb)
  obtain ⟨⟨sa, fa, fla⟩, hra, hresa⟩ := iha (args_typedT ht) hxa ha
  by_cases hn : ∃ us, o₁ = .normal us
  swap
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    exact ⟨_, .argsAbort hra (not_normal_of_res hresa hn), hresa⟩
  obtain ⟨us, rfl⟩ := hn
  have he := resOut_normal_inv hresa
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp only [ThenC] at hb
  cases hb with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | @callInd _ s₂ _ _ _ ws us' vs _ _ ad i fa' fi ps rs fl _ _ hres hfi hty hn' hcall hvs hk =>
    rw [show (ws ++ us' ++ [Val.num ⟨.int ad.intType, i⟩]).reverse =
      .num ⟨.int ad.intType, i⟩ :: (ws ++ us').reverse by simp] at hra
    obtain ⟨htk, hdr⟩ := take_rev_append (ws := ws) hn'
    obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv hk
    refine ⟨_, .callIndOk hra hres hfi hty (by rw [htk]; exact hcall) hvs .nil, rfl, rfl, ?_⟩
    rw [hdr]; simp [FlowRel]
  | @callIndTrap _ _ _ ws us' _ _ ad i fa' fi ps rs _ hres hfi hty hn' hcall =>
    rw [show (ws ++ us' ++ [Val.num ⟨.int ad.intType, i⟩]).reverse =
      .num ⟨.int ad.intType, i⟩ :: (ws ++ us').reverse by simp] at hra
    obtain ⟨htk, -⟩ := take_rev_append (ws := ws) hn'
    exact ⟨_, .callIndStop (fl := .trap) hra hres hfi hty (by rw [htk]; exact hcall)
      (by simp [Flow.Abrupt]), rfl, rfl, trivial⟩
  | @callIndThrow _ _ _ ws us' _ _ ad i fa' t fi ps rs _ hres hfi hty hn' hcall =>
    rw [show (ws ++ us' ++ [Val.num ⟨.int ad.intType, i⟩]).reverse =
      .num ⟨.int ad.intType, i⟩ :: (ws ++ us').reverse by simp] at hra
    obtain ⟨htk, -⟩ := take_rev_append (ws := ws) hn'
    exact ⟨_, .callIndStop (fl := .throw t) hra hres hfi hty (by rw [htk]; exact hcall)
      (by simp [Flow.Abrupt]), rfl, rfl, rfl⟩
  | @callIndRes _ _ ws _ _ ad i _ hres =>
    rw [show (ws ++ [Val.num ⟨.int ad.intType, i⟩]).reverse =
      .num ⟨.int ad.intType, i⟩ :: ws.reverse by simp] at hra
    exact ⟨_, .callIndRes hra hres, rfl, rfl, trivial⟩

omit hC hCk in
/-- **A reference call tree, backwards.** -/
theorem bwd1_callRef {y : TypeIdx} {args : List BExpr} (iha : BwdL o C args) :
    Bwd1 o C (.op (.callRef y) args) := by
  intro s s' f f' stk out es ht hx h
  rw [show expression (BExpr.lower (.op (.callRef y) args)) =
      expression (BExpr.lowerList args) ++ [.plain (.callRef y)] by
    simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  have hxa : tailFreeL args = true ∨ NT o₁ :=
    hx.imp (fun h => by simp only [tailFree, Bool.and_eq_true] at h; exact h.2) (nt_of_then · hb)
  obtain ⟨⟨sa, fa, fla⟩, hra, hresa⟩ := iha (args_typedT ht) hxa ha
  by_cases hn : ∃ us, o₁ = .normal us
  swap
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    exact ⟨_, .argsAbort hra (not_normal_of_res hresa hn), hresa⟩
  obtain ⟨us, rfl⟩ := hn
  have he := resOut_normal_inv hresa
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp only [ThenC] at hb
  cases hb with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | @callRef _ s₂ _ _ _ ws us' vs _ fa' fi ps rs fl _ _ hfi hty hn' hcall hvs hk =>
    rw [show (ws ++ us' ++ [Val.ref (.func fa')]).reverse =
      .ref (.func fa') :: (ws ++ us').reverse by simp] at hra
    obtain ⟨htk, hdr⟩ := take_rev_append (ws := ws) hn'
    obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv hk
    refine ⟨_, .callRefOk hra hfi hty (by rw [htk]; exact hcall) hvs .nil, rfl, rfl, ?_⟩
    rw [hdr]; simp [FlowRel]
  | @callRefTrap _ _ _ ws us' _ fa' fi ps rs _ hfi hty hn' hcall =>
    rw [show (ws ++ us' ++ [Val.ref (.func fa')]).reverse =
      .ref (.func fa') :: (ws ++ us').reverse by simp] at hra
    obtain ⟨htk, -⟩ := take_rev_append (ws := ws) hn'
    exact ⟨_, .callRefStop (fl := .trap) hra hfi hty (by rw [htk]; exact hcall)
      (by simp [Flow.Abrupt]), rfl, rfl, trivial⟩
  | @callRefThrow _ _ _ ws us' _ fa' t fi ps rs _ hfi hty hn' hcall =>
    rw [show (ws ++ us' ++ [Val.ref (.func fa')]).reverse =
      .ref (.func fa') :: (ws ++ us').reverse by simp] at hra
    obtain ⟨htk, -⟩ := take_rev_append (ws := ws) hn'
    exact ⟨_, .callRefStop (fl := .throw t) hra hfi hty (by rw [htk]; exact hcall)
      (by simp [Flow.Abrupt]), rfl, rfl, rfl⟩
  | @callRefNull _ _ ws _ _ =>
    rw [show (ws ++ [Val.ref .null]).reverse = .ref .null :: ws.reverse by simp] at hra
    exact ⟨_, .callRefNull hra, rfl, rfl, trivial⟩

omit hC hCk in
/-- **A tail call tree whose region outcome is not a pending tail call of a function**: a
`return_call_ref` on null (a pending tail call of null) or a `return_call_indirect` without a
callee (`run_rci_inv`); either way the native evaluator traps (`EvalOX.tailRes`). -/
theorem bwd1_tail {i : Instr} {args : List BExpr} (hi : isTailCall i = true)
    (iha : BwdL o C args) : Bwd1 o C (.op i args) := by
  intro s s' f f' stk out es ht hx h
  have hnt : NT out := hx.resolve_left (by simp [tailFree, hi])
  rw [show expression (BExpr.lower (.op i args)) =
      expression (BExpr.lowerList args) ++ [.plain i] by simp [BExpr.lower, expression]] at h
  obtain ⟨s₁, f₁, o₁, ha, hb⟩ := Proofs.Region.run_split h rfl
  obtain ⟨⟨sa, fa, fla⟩, hra, hresa⟩ := iha (args_typedT ht) (.inr (nt_of_then hnt hb)) ha
  by_cases hn : ∃ us, o₁ = .normal us
  swap
  · simp only [not_exists] at hn
    obtain ⟨rfl, rfl, rfl⟩ := thenC_stop_inv hn hb
    exact ⟨_, .argsAbort hra (not_normal_of_res hresa hn), hresa⟩
  obtain ⟨us, rfl⟩ := hn
  have he := resOut_normal_inv hresa
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp only [ThenC] at hb
  cases i <;> simp only [isTailCall, reduceCtorEq] at hi
  · cases hb with
    | returnCall hfi => exact absurd rfl (hnt _ _ _)
    | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
    | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
    | val hv => simp [Admin.val?] at hv
    | simple hi => simp [SingleThreaded.Det.famOf] at hi
    | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
    | brData hb => cases hb
  · cases hb with
    | returnCallRef hc => exact absurd rfl (hnt _ _ _)
    | @returnCallRefNull _ _ ws c _ hc =>
      rw [show (ws ++ [Val.ref .null]).reverse = .ref .null :: ws.reverse by simp] at hra
      exact ⟨_, .tailRes hra .refNull, rfl, rfl, trivial⟩
    | val hv => simp [Admin.val?] at hv
    | simple hi => simp [SingleThreaded.Det.famOf] at hi
    | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
    | brData hb => cases hb
  · obtain ⟨W, a, i', rfl, hres, rfl, rfl, hout⟩ := run_rci_inv hb hnt
    rw [show (W ++ [Val.num ⟨.int a.intType, i'⟩]).reverse =
      .num ⟨.int a.intType, i'⟩ :: W.reverse by simp] at hra
    refine ⟨_, .tailRes hra (.indirectTrap hres), ?_⟩
    rcases hout with rfl | ⟨c, rfl⟩ <;> exact ⟨rfl, rfl, trivial⟩

omit hC hCk in
/-- `try_table` does not pass the tail checker, so it has no typed backward case to prove. -/
theorem bwd1_tryTable {bt : BlockType} {cs : List Catch} {body : List BExpr} :
    Bwd1 o C (.tryTable bt cs body) := by
  intro s s' f f' stk out es ht hx h
  obtain ⟨rest, labels, ret, out', hS, hc, -, -, -⟩ := ht
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hc
  simp [chk1E, tExt] at h1


/-- **An operator tree, backwards**: a direct, indirect or reference call, or a flat
instruction; tail calls are outside the fragment. -/
theorem bwd1_op {i : Instr} {args : List BExpr} (iha : BwdL o C args) :
    Bwd1 o C (.op i args) := by
  intro s s' f f' stk out es ht hx h
  rcases Classical.em (∃ x, i = .call x) with ⟨x, rfl⟩ | hcall
  · exact bwd1_call iha ht hx h
  cases htc : isTailCall i
  swap
  · exact bwd1_tail htc iha ht hx h
  cases hxi : isXCall i
  · exact bwd1_op_flat hC hCk (fun x hx => hcall ⟨x, hx⟩) hxi iha ht hx h
  · cases i <;> simp only [isXCall, isTailCall, reduceCtorEq] at hxi htc <;>
      first
        | exact bwd1_callInd iha ht hx h
        | exact bwd1_callRef iha ht hx h

omit hC hCk in
theorem bwdL_nil : BwdL o C [] := by
  intro s s' f f' stk out ht hx h
  obtain ⟨rfl, rfl, rfl⟩ :=
    Proofs.Region.run_nil_inv (by simpa [BExpr.lowerList, expression] using h)
  exact ⟨_, .nil, rfl, rfl, by simp [FlowRel]⟩

/-- **The tree-level backward bridge without extended calls**, by induction on the size of the
trees (loops by induction on their region run, `loop_aux`). -/
theorem bwdL_all : ∀ es, BwdL o C es := by
  intro es
  induction hn : sizeOf es using Nat.strong_induction_on generalizing es with
  | _ n ih =>
  cases es with
  | nil => exact bwdL_nil
  | cons e es =>
    have hs : sizeOf (e :: es) = 1 + sizeOf e + sizeOf es := rfl
    have ihe : ∀ es', sizeOf es' < sizeOf e → BwdL o C es' := fun es' hl =>
      ih (sizeOf es') (by omega) es' rfl
    have ihr : BwdL o C es := ih (sizeOf es) (by omega) es rfl
    have h1 : Bwd1 o C e := by
      cases e with
      | op i args => exact bwd1_op hC hCk (ihe args (by simp))
      | block bt body => exact bwd1_block hC hCk (ihe body (by simp))
      | loop bt body => exact bwd1_loop hC hCk (ihe body (by simp))
      | if_ bt c t el =>
        exact bwd1_if hC hCk (ihe c (by simp; omega)) (ihe t (by simp; omega))
          (ihe el (by simp))
      | tryTable bt cs body => exact bwd1_tryTable
    intro s s' f f' stk out
    exact bwd_cons hC hCk h1 ihr
end Main

end Silmaril.Wasm.Cfg.Proofs.Bridge
