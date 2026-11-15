module

public import Silmaril.Proofs.Wasm.Interp.Total
public import Silmaril.Proofs.Wasm.Interp.DivergeBasic

/-!
# Typed native problems that do not evaluate diverge (proofs)

A *good* native problem satisfies the invariants of
`Silmaril.Proofs.Wasm.Interp.Total`:

* it passes the arity check;
* its Core code is typed in context;
* the store is native and arity-checked.

`bad_step`: a good problem without a native evaluation unfolds into a
divergence step (`DivStep`), and the parts it hands on are again good
problems without an evaluation. Typing rules out every way of getting
stuck, exactly as in `Total` (`evalFlat_progress`, `truthy_progress`,
`callArity_func?`, `callee_flow`). So, by coinduction, `bad_le_evalDiv`
holds: a good problem without an evaluation diverges.

The case analysis follows `Total.term_step`. Where `Total` asks its
induction hypothesis for a sub-evaluation, this file builds the
sub-problem's invariants and splits on whether it evaluates.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Execution.Core.Sim

variable {H : Type}

/-- The deterministic profile used for the Core side of the invariants. -/
abbrev o₀ : GrowOracle := fun _ _ _ _ => false

/-- A native problem with the invariants of `Total`. -/
def Good (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Prop :=
  ∃ (labels : List Nat) (ret : Nat) (out : Option Nat),
    chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out ∧
    ContextTyped (pcfg s f stk es) ∧ Binaryen.NativeFuncsOk s.funcs ∧ StoreChk s.funcs

/-- A good problem without a native evaluation. -/
def Bad (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Prop :=
  Good s f stk es ∧ ¬ ∃ r, Binaryen.Eval s f stk es r

section Cases

variable {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}

/-- Split a good problem on whether it evaluates. -/
theorem good_split {s' : Store H} {f' : Frame} {stk' : List Val} {es' : List Binaryen.BExpr}
    (hg : Good s' f' stk' es') : Bad s' f' stk' es' ∨ ∃ r, Binaryen.Eval s' f' stk' es' r := by
  by_cases h : ∃ r, Binaryen.Eval s' f' stk' es' r
  · exact .inr h
  · exact .inl ⟨hg, h⟩

/-- The parts of a block (or an `if` arm): the body is good, and so is the
continuation after every body result handing on values. -/
theorem block_good {P₀ : Config H} {bt : BlockType}
    {body : List Binaryen.BExpr} {np nr : Nat} {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hrun : Relation.ReflTransGen (Step (profile o₀) Det.noHost) P₀
      ⟨s, f, vals stk.reverse ++ .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩)
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : endsAt (chk s.funcs f.module f.locals.length ret (nr :: labels) (some np) body) nr = true)
    (h2 : chk s.funcs f.module f.locals.length ret labels (some (stk.length - np + nr)) es =
      some out)
    (ht : ContextTyped P₀) (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) :
    Good s f (stk.take np) body ∧
      ∀ s₁ f₁ fl vs, Binaryen.Eval s f (stk.take np) body (s₁, f₁, fl) →
        fl.blockVals = some vs → Good s₁ f₁ (vs.take nr ++ stk.drop np) es := by
  have enter := step_enter (P := profile o₀) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_block har) (expression (Binaryen.BExpr.lowerList es))
  have hrun₁ : Relation.ReflTransGen (Step (profile o₀) Det.noHost) P₀
      (mapLabel (stk.drop np).reverse nr [] (expression (Binaryen.BExpr.lowerList es))
        (pcfg s f (stk.take np) body)) := hrun.tail enter
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  have hbc : chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]
    exact hb'
  have ht₁ : ContextTyped (pcfg s f (stk.take np) body) :=
    ContextTyped.label (ContextTyped.steps ht hrun₁)
  refine ⟨⟨nr :: labels, ret, ob, hbc, ht₁, hF, hS⟩, fun s₁ f₁ fl vs hbody hvs => ?_⟩
  obtain ⟨hok, inv1⟩ := flowOk_of_eval hbody hS hbc
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  obtain ⟨c', o', hr, he, hm⟩ :=
    run_of_wp (wp_of_eval (P := profile o₀) (host := Det.noHost) hbody hS hbc)
  have htg := tg_block_vals (rest := expression (Binaryen.BExpr.lowerList es)) har hp hr he hm
    hvs hnr hnorm
  have hrun₂ : Relation.ReflTransGen (Step (profile o₀) Det.noHost) P₀
      (pcfg s₁ f₁ (vs.take nr ++ stk.drop np) es) := hrun.trans htg.to_reflTransGen
  exact ⟨labels, ret, out, chk_after inv1 hp hnr h2, ContextTyped.steps ht hrun₂,
    nativeFuncsOk_inv inv1 hF, storeChk_inv inv1 hS⟩

/-- **Operators other than calls.** -/
theorem bad_op {i : Instr} {args : List Binaryen.BExpr} (hi : ∀ x, i ≠ .call x)
    (hbad : Bad s f stk (.op i args :: es)) : DivStep Bad Bad s f stk (.op i args :: es) := by
  obtain ⟨⟨labels, ret, out, hc, ht, hF, hS⟩, hne⟩ := hbad
  obtain ⟨o₁, h1, h2⟩ := chk_cons.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  have hta : ContextTyped (pcfg s f stk args) := by
    rw [pcfg_op] at ht
    exact ContextTyped.suffix ht
  rcases good_split ⟨labels, ret, oa, ha, hta, hF, hS⟩ with hb | ⟨⟨s₁, f₁, fl⟩, hargs⟩
  · exact .args hb
  by_cases hn : fl.IsNormal
  swap
  · exact absurd ⟨_, .argsAbort hargs hn⟩ hne
  rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
  obtain ⟨hf, inv1⟩ := arity_args hS (flowOk_of_eval hargs) h1
  have hrun : Relation.ReflTransGen (Step (profile o₀) Det.noHost)
      (pcfg s f stk (.op i args :: es))
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: expression (Binaryen.BExpr.lowerList es)⟩ := by
    rw [pcfg_op]
    exact (sp_suffix _).steps (run_normal hargs hS ha)
  have hF₁ : Binaryen.NativeFuncsOk s₁.funcs := nativeFuncsOk_inv inv1 hF
  obtain ⟨⟨s₂, f₂, fl₂⟩, hflat⟩ := evalFlat_progress hf hi (ContextTyped.steps ht hrun) hF₁
  by_cases hn₂ : fl₂.IsNormal
  swap
  · exact absurd ⟨_, .opStop hi hargs hflat hn₂⟩ hne
  rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn₂
  obtain ⟨ho, inv2⟩ := flat_normal hflat hf
  have inv12 : EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
  have hst := steps_flat_normal (P := profile o₀) (host := Det.noHost) hi hf hflat
    (expression (Binaryen.BExpr.lowerList es))
  have hrun₂ : Relation.ReflTransGen (Step (profile o₀) Det.noHost)
      (pcfg s f stk (.op i args :: es)) (pcfg s₂ f₂ stk₂ es) := hrun.trans hst
  have h2' : chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
      some out := by
    rw [← ho]
    exact chk_inv inv12 h2
  rcases good_split ⟨labels, ret, out, h2', ContextTyped.steps ht hrun₂, nativeFuncsOk_inv inv12 hF,
    storeChk_inv inv12 hS⟩ with hb | ⟨r, hk⟩
  · exact .opK hi hargs hflat hb
  · exact absurd ⟨r, .opOk hi hargs hflat hk⟩ hne

/-- **Direct calls.** -/
theorem bad_call {x : FuncIdx} {args : List Binaryen.BExpr}
    (hbad : Bad s f stk (.op (.call x) args :: es)) :
    DivStep Bad Bad s f stk (.op (.call x) args :: es) := by
  obtain ⟨⟨labels, ret, out, hc, ht, hF, hS⟩, hne⟩ := hbad
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  have hta : ContextTyped (pcfg s f stk args) := by
    rw [pcfg_op] at ht
    exact ContextTyped.suffix ht
  rcases good_split ⟨labels, ret, oa, ha, hta, hF, hS⟩ with hb | ⟨⟨s₁, f₁, fl⟩, hargs⟩
  · exact .args hb
  by_cases hn : fl.IsNormal
  swap
  · exact absurd ⟨_, .argsAbort hargs hn⟩ hne
  rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
  obtain ⟨hf, inv1⟩ := arity_args hS (flowOk_of_eval hargs) h1
  obtain ⟨p, q, hpq, -, -⟩ := flatChk_call hf
  obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := callArity_func? hpq
  obtain ⟨-, hp, h2⟩ := arity_call_pre hS (flowOk_of_eval hargs) hfi hty hc
  have hF₁ : Binaryen.NativeFuncsOk s₁.funcs := nativeFuncsOk_inv inv1 hF
  have hS₁ : StoreChk s₁.funcs := storeChk_inv inv1 hS
  obtain ⟨fn, hcode, -⟩ := hF₁ fi (List.mem_of_getElem? (funcs_of_func? hfi))
  have hrun : Relation.ReflTransGen (Step (profile o₀) Det.noHost)
      (pcfg s f stk (.op (.call x) args :: es))
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    rw [pcfg_op]
    exact (sp_suffix _).steps (run_normal hargs hS ha)
  -- the callee is a good problem
  have enter := steps_call_enter (P := profile o₀) (host := Det.noHost) hfi hcode hty hp
    (expression (Binaryen.BExpr.lowerList es))
  rw [pcfg_callee] at enter
  have htg := Relation.TransGen.trans_right hrun enter
  have hct : ContextTyped (pcfg s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)) :=
    ContextTyped.label (ContextTyped.frame (ContextTyped.steps ht htg.to_reflTransGen))
  obtain ⟨ob, hob, hb'⟩ := callee_chk (ext := noExt) hS₁ hfi hcode hty hp
  rcases good_split ⟨_, _, _, hb', hct, hF₁, hS₁⟩ with hb | ⟨⟨s₂, f₂, flb⟩, hbody⟩
  · exact .callee hargs hfi hcode hty hb
  obtain ⟨hok, hinvb⟩ := flowOk_of_eval hbody hS₁ hb'
  rcases callee_flow hok with ⟨vs, hvs⟩ | rfl | ⟨t, rfl⟩
  · -- the continuation after the return is a good problem
    have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    have hnorm : ∀ ws, flb = .normal ws → ws.length = rs.length := by
      rintro ws rfl
      exact length_of_ends hok hob
    obtain ⟨c', o', hrunb, he, hm⟩ :=
      run_of_wp (wp_of_eval (P := profile o₀) (host := Det.noHost) hbody hS₁ hb')
    have hrunb' : Relation.ReflTransGen (Step (profile o₀) Det.noHost)
        ⟨s₁, calleeFrame fi fn stk₁ ps.length, expression fn.body⟩ ⟨s₂, f₂, c'⟩ := by
      simpa [vals, Binaryen.lowerList_liftInstrs] using hrunb
    have htg₂ := Relation.TransGen.trans_right hrun
      (tg_call_ok hfi hcode hty hp hrunb' he hm hvs hrs hnorm)
    have inv2 : EvalInv s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
      ⟨inv1.1.trans hinvb.1, inv1.2.1, inv1.2.2⟩
    have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
        stk₁.length - ps.length + rs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    have h2' : chk s₂.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
      rw [hlen]
      exact chk_inv inv2 h2
    rcases good_split ⟨labels, ret, out, h2', ContextTyped.steps ht htg₂.to_reflTransGen,
      nativeFuncsOk_inv inv2 hF, storeChk_inv inv2 hS⟩ with hb | ⟨r, hk⟩
    · exact .callRet hargs hfi hcode hty hbody hvs hb
    · exact absurd ⟨r, .callOk hargs hfi hcode hty hbody hvs hk⟩ hne
  · exact absurd ⟨_, .callTrap hargs hfi hcode hty hbody⟩ hne
  · exact absurd ⟨_, .callThrow hargs hfi hcode hty hbody⟩ hne

/-- **Blocks.** -/
theorem bad_block {bt : BlockType} {body : List Binaryen.BExpr}
    (hbad : Bad s f stk (.block bt body :: es)) : DivStep Bad Bad s f stk (.block bt body :: es) := by
  obtain ⟨⟨labels, ret, out, hc, ht, hF, hS⟩, hne⟩ := hbad
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_block h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨hp, hb, h2⟩ := arity_block_pre har hc
  obtain ⟨hgb, hgk⟩ := block_good (by rw [pcfg_block]) har hp hb h2 ht hF hS
  rcases good_split hgb with hb | ⟨⟨s₁, f₁, fl⟩, hbody⟩
  · exact .block har hb
  rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
  · rcases good_split (hgk _ _ _ _ hbody hvs) with hb | ⟨r, hk⟩
    · exact .blockK har hbody hvs hb
    · exact absurd ⟨r, .blockOk har hbody hvs hk⟩ hne
  · exact absurd ⟨_, .blockBrk har hbody⟩ hne
  · exact absurd ⟨_, .blockEsc har hbody hesc⟩ hne

/-- **Conditionals.** -/
theorem bad_if {bt : BlockType} {c t el : List Binaryen.BExpr}
    (hbad : Bad s f stk (.if_ bt c t el :: es)) : DivStep Bad Bad s f stk (.if_ bt c t el :: es) := by
  obtain ⟨⟨labels, ret, out, hc, ht, hF, hS⟩, hne⟩ := hbad
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oc, hco, hk1⟩ := chk1_if h1
  have htc : ContextTyped (pcfg s f stk c) := by
    rw [pcfg_if] at ht
    exact ContextTyped.suffix ht
  rcases good_split ⟨labels, ret, oc, hco, htc, hF, hS⟩ with hb | ⟨⟨s₁, f₁, fl⟩, hcond⟩
  · exact .cond hb
  by_cases hn : fl.IsNormal
  swap
  · exact absurd ⟨_, .ifAbort hcond hn⟩ hne
  rcases fl with stk₁' | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
  obtain ⟨hoc, inv1⟩ := flowOk_of_eval hcond hS hco
  obtain ⟨np, nr, ha, -, -, -, -⟩ := hk1 _ hoc
  have hrun₁ : Relation.ReflTransGen (Step (profile o₀) Det.noHost)
      (pcfg s f stk (.if_ bt c t el :: es))
      ⟨s₁, f₁, vals stk₁'.reverse ++ .plain (.if_ bt (Binaryen.BExpr.lowerList t)
        (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)⟩ := by
    rw [pcfg_if]
    exact (sp_suffix _).steps (run_normal hcond hS hco)
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := truthy_progress (ContextTyped.steps ht hrun₁) (nativeFuncsOk_inv inv1 hF)
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [arity_eq, inv1.2.1]
    exact ha
  obtain ⟨inv1', hp, hbarm, h2⟩ := arity_if_pre (b := b) hS (flowOk_of_eval hcond) har hc
  replace hbarm := chk_inv_endsAt inv1' hbarm
  replace h2 := chk_inv inv1' h2
  have hrun₂ := hrun₁.tail (step_if_arm (o := o₀) (rest := expression (Binaryen.BExpr.lowerList es)) hb)
  obtain ⟨hga, hgk⟩ := block_good hrun₂ har hp hbarm h2 ht (nativeFuncsOk_inv inv1' hF) (storeChk_inv inv1' hS)
  rcases good_split hga with hba | ⟨⟨s₂, f₂, fl⟩, harm⟩
  · exact .arm hcond hb har hba
  rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
  · rcases good_split (hgk _ _ _ _ harm hvs) with hbk | ⟨r, hk⟩
    · exact .ifK hcond hb har harm hvs hbk
    · exact absurd ⟨r, .ifOk hcond hb har harm hvs hk⟩ hne
  · exact absurd ⟨_, .ifBrk hcond hb har harm⟩ hne
  · exact absurd ⟨_, .ifEsc hcond hb har harm hesc⟩ hne

/-- **Loops.** -/
theorem bad_loop {bt : BlockType} {body : List Binaryen.BExpr}
    (hbad : Bad s f stk (.loop bt body :: es)) : DivStep Bad Bad s f stk (.loop bt body :: es) := by
  obtain ⟨⟨labels, ret, out, hc, ht, hF, hS⟩, hne⟩ := hbad
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_loop h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hc
  have enter := step_enter (P := profile o₀) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har) (expression (Binaryen.BExpr.lowerList es))
  have hrun₁ : Relation.ReflTransGen (Step (profile o₀) Det.noHost)
      (pcfg s f stk (.loop bt body :: es))
      (mapLabel (stk.drop np).reverse np [.loop bt (Binaryen.BExpr.lowerList body)]
        (expression (Binaryen.BExpr.lowerList es)) (pcfg s f (stk.take np) body)) := by
    rw [pcfg_loop]
    exact .single enter
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  have hbc : chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]
    exact hb'
  rcases good_split ⟨np :: labels, ret, ob, hbc, ContextTyped.label (ContextTyped.steps ht hrun₁),
    hF, hS⟩ with hbb | ⟨⟨s₁, f₁, fl⟩, hbody⟩
  · exact .loop har hbb
  obtain ⟨hok, inv1⟩ := flowOk_of_eval hbody hS hbc
  obtain ⟨c', o', hr, he, hm⟩ :=
    run_of_wp (wp_of_eval (P := profile o₀) (host := Det.noHost) hbody hS hbc)
  rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
  · have hlen : vs.length = nr := length_of_ends hok hob
    have htg := tg_loop_normal (rest := expression (Binaryen.BExpr.lowerList es)) har hp hr he hm
      hlen
    rw [← pcfg_loop] at htg
    rcases good_split ⟨labels, ret, out, chk_after inv1 hp hlen.ge h2,
      ContextTyped.steps ht htg.to_reflTransGen, nativeFuncsOk_inv inv1 hF, storeChk_inv inv1 hS⟩ with hbk | ⟨r, hk⟩
    · exact .loopK har hbody hbk
    · exact absurd ⟨r, .loopOk har hbody hk⟩ hne
  · obtain ⟨m, hm', hle⟩ := hok
    have hnp : np ≤ vs.length := by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm'
      exact hm' ▸ hle
    have htg := tg_loop_back (rest := expression (Binaryen.BExpr.lowerList es)) har hp hr he hm hnp
    rw [← pcfg_loop] at htg
    rw [← pcfg_loop] at htg
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    have hc' : chk s₁.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
      rw [hlen]
      exact chk_inv inv1 hc
    rcases good_split ⟨labels, ret, out, hc', ContextTyped.steps ht htg.to_reflTransGen,
      nativeFuncsOk_inv inv1 hF, storeChk_inv inv1 hS⟩ with hbk | ⟨r, hk⟩
    · exact .loopBack har hbody hbk
    · exact absurd ⟨r, .loopBack har hbody hk⟩ hne
  · exact absurd ⟨_, .loopBrk har hbody⟩ hne
  · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
  · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne
  · exact absurd ⟨_, .loopEsc har hbody trivial⟩ hne

/-- **One unfolding**: a good problem without an evaluation takes a divergence
step into good problems without an evaluation. -/
theorem bad_step (hbad : Bad s f stk es) : DivStep Bad Bad s f stk es := by
  rcases es with _ | ⟨e, es⟩
  · exact absurd ⟨_, .nil⟩ hbad.2
  · cases e with
    | op i args =>
      by_cases hi : ∃ x, i = .call x
      · obtain ⟨x, rfl⟩ := hi
        exact bad_call hbad
      · exact bad_op (fun x hx => hi ⟨x, hx⟩) hbad
    | block bt body => exact bad_block hbad
    | loop bt body => exact bad_loop hbad
    | if_ bt c t el => exact bad_if hbad
    | tryTable bt cs body =>
      obtain ⟨⟨labels, ret, out, hc, -⟩, -⟩ := hbad
      obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
      simp[chk1, chk1E, noExt] at h1

end Cases

/-- **A good problem without a native evaluation diverges.** -/
theorem bad_le_evalDiv : (Bad : Problem H) ≤ EvalDiv :=
  evalDiv_coind fun _ _ _ _ h => bad_step h

end Silmaril.Wasm.Interp
