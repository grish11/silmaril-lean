module

public import Silmaril.Wasm.Cfg.Bridge.Defs
public import Silmaril.Proofs.Wasm.Cfg.RegionDivC
public import Silmaril.Wasm.Interp.OracleX.Thms
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Wasm.Abstract.CallXT.Thms
public import Silmaril.Wasm.Cfg.MachineClosedX.Defs

@[expose] public section

/-!
# The bridge from extended native trees to the region semantics: proofs

Forward direction: a typed (`EvalOXT`), checked (`chkE tExt`) native run with a sound oracle is a
region run of the lowered code with the same oracle, ending as `ResOut` says. By induction on the
native derivation; the checker facts and arities at each node are Interp's
(`chk_consE`, `arity_args`, `arity_call_pre`, `arity_block_pre`, `body_facts`, …, through the
public `Interp.OracleX.Thms`), and a flat instruction's step is the Core agreement
`flat_core_normal`/`flat_core_abrupt` (`Interp.Thms`), read back as a region run by region completeness on the
call-free fragment.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Bridge

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp

set_option linter.unusedSimpArgs false

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-! ## Outcomes -/

/-- A Core-logic outcome as a region outcome (same constructors). -/
def ofOutcome : Logic.Core.Outcome → Region.Out
  | .normal vs => .normal vs
  | .br l vs => .br l vs
  | .ret vs => .ret vs
  | .trap => .trap
  | .throw a => .throw a
  | .tail vs a c => .tail vs a c
  | .tailNull vs c => .tailNull vs c

theorem ends_ofOutcome {o : Logic.Core.Outcome} {c : List Admin} (h : o.Ends c) :
    (ofOutcome o).Ends c := by
  cases o <;> exact h

/-! ## Flat instructions -/

/-- Every instruction the native evaluator runs is in the call-free fragment. -/
theorem fragI_of_evalFlat {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {r : Store H × Frame × Flow} (h : evalFlat s f stk i = some r) : Region.FragI i := by
  cases i
  all_goals first
    | exact Region.FragIB.br _
    | exact Region.FragIB.brIf _
    | exact Region.FragIB.return_
    | (apply Region.FragIB.brData; simp [Instr.IsBrData]; done)
    | (apply Region.FragIB.const; simp [Admin.val?]; done)
    | (apply Region.FragIB.simple; simp [SingleThreaded.Det.famOf]; done)
    | (exfalso; unfold evalFlat at h; simp at h)

/-- A call-free region run is one with any oracle. -/
theorem runC_of_frag {s s' : Store H} {f f' : Frame} {code c' : List Admin} {o : Region.Out}
    (hF : Region.Frag code) (h : Steps P host ⟨s, f, code⟩ ⟨s', f', c'⟩) (he : o.Ends c') :
    RunC P host C s f [] code s' f' o :=
  Proofs.Region.completeC (G := fun _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ _ _ hg => hg.elim)
    (Proofs.Region.guardedCalls_frag hF) (fun a ha => Proofs.Region.fragAB_true (hF a ha)) h he

/-- **A checked flat instruction is a region step** (any oracle): its native result, as a
region outcome. -/
theorem flat_run {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Flow}
    {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat} {labels : List Nat} {h₀ : Nat}
    {o : Option Nat} (hi : ∀ x, i ≠ .call x) (hf : flatChk F mi f.locals.length ret labels h₀ i = some o)
    (h : evalFlat s f stk i = some (s', f', fl)) :
    ∃ o', RunC P host C s f stk.reverse [.plain i] s' f' o' ∧ FlowRel fl o' ∧
      ∀ W a c, o' ≠ .tail W a c := by
  have hF : Region.Frag (vals stk.reverse ++ [.plain i]) :=
    Proofs.Region.frag_append.2 ⟨Proofs.Region.frag_vals _, fun a ha => by
      simp only [List.mem_singleton] at ha; subst ha; exact .plain (fragI_of_evalFlat h)⟩
  by_cases hn : fl.IsNormal
  · obtain ⟨stk', rfl⟩ : ∃ stk', fl = .normal stk' := by
      cases fl <;> simp_all [Flow.IsNormal]
    have hs := flat_core_normal (P := P) (host := host) hi hf h []
    have hr := runC_of_frag (C := C) (o := .normal stk'.reverse) hF (by simpa using hs) rfl
    exact ⟨_, by simpa using Proofs.Region.run_vals_inv (vs := []) hr, by simp [FlowRel], by simp⟩
  · obtain ⟨s₂, f₂, c', oc, hs, he, rfl, rfl, hm⟩ := flat_core_abrupt (P := P) (host := host) hf h hn []
    have hr := runC_of_frag (C := C) (o := ofOutcome oc) hF (by simpa using hs) (ends_ofOutcome he)
    refine ⟨_, by simpa using Proofs.Region.run_vals_inv (vs := []) hr, ?_, ?_⟩
    · cases fl <;> cases oc <;> simp_all [FlowMatch, FlowRel, ofOutcome]
    · intro W a c hc
      cases fl <;> cases oc <;> simp_all [FlowMatch, ofOutcome]

/-! ## Resolved ends -/

theorem tailFlow_ne_normal (n : Nat) (fl : Flow) (vs : List Val) :
    Abstract.CallX.tailFlow n fl ≠ .normal vs := by
  cases fl with
  | brk k _ => cases k <;> simp [Abstract.CallX.tailFlow]
  | _ => simp [Abstract.CallX.tailFlow]

theorem tailFlow_ne_brk (n : Nat) (fl : Flow) (l : Nat) (vs : List Val) :
    Abstract.CallX.tailFlow n fl ≠ .brk l vs := by
  cases fl with
  | brk k _ => cases k <;> simp [Abstract.CallX.tailFlow]
  | _ => simp [Abstract.CallX.tailFlow]

theorem resOut_of_rel {s : Store H} {f : Frame} {o : Region.Out} {fl : Flow}
    (hnt : ∀ W a c, o ≠ .tail W a c) (h : FlowRel fl o) : ResOut C s f o (s, f, fl) := by
  cases o with
  | tail W a c => exact absurd rfl (hnt W a c)
  | _ => exact ⟨rfl, rfl, h⟩

theorem resOut_normal {s' s₁ : Store H} {f' f₁ : Frame} {o : Region.Out} {vs : List Val}
    (h : ResOut C s' f' o (s₁, f₁, .normal vs)) : o = .normal vs.reverse ∧ s' = s₁ ∧ f' = f₁ := by
  cases o with
  | tail W a c =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := h
    exact absurd he.symm (tailFlow_ne_normal _ _ _)
  | normal ws => obtain ⟨rfl, rfl, h⟩ := h; simp only [FlowRel] at h; exact ⟨by rw [h], rfl, rfl⟩
  | _ => obtain ⟨rfl, rfl, h⟩ := h; simp [FlowRel] at h

theorem resOut_brk {s' s₁ : Store H} {f' f₁ : Frame} {o : Region.Out} {l : Nat} {vs : List Val}
    (h : ResOut C s' f' o (s₁, f₁, .brk l vs)) :
    s' = s₁ ∧ f' = f₁ ∧ ∃ junk, o = .br l (junk ++ vs.reverse) := by
  cases o with
  | tail W a c =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := h
    exact absurd he.symm (tailFlow_ne_brk _ _ _ _)
  | br l' ws =>
    obtain ⟨rfl, rfl, h⟩ := h; simp only [FlowRel] at h
    obtain ⟨rfl, junk, rfl⟩ := h; exact ⟨rfl, rfl, junk, rfl⟩
  | _ => obtain ⟨rfl, rfl, h⟩ := h; simp [FlowRel] at h

theorem resOut_not_normal {s' : Store H} {f' : Frame} {o : Region.Out} {r : Store H × Frame × Flow}
    (h : ResOut C s' f' o r) (hfl : ¬ r.2.2.IsNormal) : ∀ us, o ≠ .normal us := by
  rintro us rfl
  obtain ⟨-, -, h⟩ := h
  cases hr : r.2.2 <;> simp_all [FlowRel, Flow.IsNormal]

theorem thenC_stop {s : Store H} {f : Frame} {o : Region.Out} {B : List Admin}
    (h : ∀ us, o ≠ .normal us) : ThenC P host C s f o B s f o := by
  cases o with
  | normal us => exact absurd rfl (h us)
  | _ => exact ⟨rfl, rfl, rfl⟩

/-- **Leaving a label abruptly**: a deeper branch loses one label; a return, trap, exception or
pending (null) tail call passes through, collecting the label's outer values. -/
theorem label_abrupt {s s' s₁ : Store H} {f f' f₁ : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {inner code : List Admin} {o : Region.Out} {fl fl' : Flow}
    (hin : RunC P host C s f [] inner s' f' o) (hres : ResOut C s' f' o (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    ∃ o', RunC P host C s f ws (.label n cont inner :: code) s' f' o' ∧
      ResOut C s' f' o' (s₁, f₁, fl') := by
  rcases hfl with ⟨k, vs, rfl, rfl⟩ | ⟨hesc, rfl⟩
  · obtain ⟨rfl, rfl, junk, rfl⟩ := resOut_brk hres
    exact ⟨_, .labelBrSucc hin, rfl, rfl, rfl, ws ++ junk, by simp⟩
  · cases o with
    | normal us =>
      obtain ⟨rfl, rfl, h⟩ := hres; simp only at h; cases fl' <;> simp_all [FlowRel, Flow.Escapes]
    | br l us =>
      obtain ⟨rfl, rfl, h⟩ := hres; simp only at h; cases fl' <;> simp_all [FlowRel, Flow.Escapes]
    | ret us =>
      obtain ⟨rfl, rfl, h⟩ := hres
      simp only at h hin ⊢
      cases fl' <;> simp only [FlowRel] at h
      obtain ⟨junk, rfl⟩ := h
      exact ⟨_, .labelRet hin, rfl, rfl, ws ++ junk, by simp⟩
    | trap =>
      obtain ⟨rfl, rfl, h⟩ := hres
      exact ⟨_, .labelTrap hin, rfl, rfl, h⟩
    | throw a =>
      obtain ⟨rfl, rfl, h⟩ := hres
      exact ⟨_, .labelThrow hin, rfl, rfl, h⟩
    | tail W a c =>
      obtain ⟨fi, ps, rs, W₀, args, fl₀, hfi, hty, rfl, hn, hcall, hfl₀, rfl, he⟩ := hres
      exact ⟨_, .labelTail hin, fi, ps, rs, ws ++ W₀, args, fl₀, hfi, hty, by simp, hn, hcall,
        hfl₀, rfl, he⟩
    | tailNull W c =>
      obtain ⟨rfl, rfl, h⟩ := hres
      refine ⟨_, .labelTailNull hin, rfl, rfl, ?_⟩
      simp only at h ⊢; cases fl' <;> simp_all [FlowRel]

theorem rev_split (stk : List Val) (n : Nat) :
    stk.reverse = (stk.drop n).reverse ++ (stk.take n).reverse := by
  rw [← List.reverse_append, List.take_append_drop]

/-! ## Blocks, loops and conditionals -/

section Blocks

variable {s s' s₁ s₂ : Store H} {f f' f₁ f₂ : Frame} {stk vs : List Val} {bt : BlockType}
  {B : List Instr} {code : List Admin} {np nr : Nat} {o o₂ : Region.Out} {fl : Flow}

theorem len_rev_take (hp : np ≤ stk.length) : (stk.take np).reverse.length = np := by
  simp only [List.length_reverse, List.length_take]; omega

/-- A block whose body hands values `vs` to its continuation. -/
theorem block_cont (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hin : RunC P host C s f (stk.take np).reverse (expression B) s' f' o)
    (hres : ResOut C s' f' o (s₁, f₁, fl)) (hvs : fl.blockVals = some vs) (hnr : nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (hk : RunC P host C s₁ f₁ (vs.take nr ++ stk.drop np).reverse code s₂ f₂ o₂) :
    RunC P host C s f stk.reverse (.plain (.block bt B) :: code) s₂ f₂ o₂ := by
  obtain ⟨t₁, t₂, hbt, rfl, rfl⟩ := blockType_of_arity har
  rw [rev_split stk t₁.length]
  refine RunC.block hbt (len_rev_take hp) ?_
  have hin' := Proofs.Region.run_vals (vs := []) (by simpa using hin)
  rw [List.reverse_append] at hk
  cases fl with
  | normal ws =>
    simp only [Flow.blockVals, Option.some.injEq] at hvs; subst ws
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    have hl := hnorm _ rfl
    rw [List.take_of_length_le (le_of_eq hl)] at hk
    exact .labelNormal hin' hk
  | brk k ws =>
    cases k with
    | succ k => simp [Flow.blockVals] at hvs
    | zero =>
      simp only [Flow.blockVals, Option.some.injEq] at hvs; subst ws
      obtain ⟨rfl, rfl, junk, rfl⟩ := resOut_brk hres
      rw [rev_split vs t₂.length, ← List.append_assoc] at hin'
      have hk' := Proofs.Region.run_vals hk
      exact .labelBr0 hin' (len_rev_take hnr) (by simpa [expression] using hk')
  | _ => simp [Flow.blockVals] at hvs

/-- A block whose body ends abruptly. -/
theorem block_abrupt {fl' : Flow} (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hin : RunC P host C s f (stk.take np).reverse (expression B) s' f' o)
    (hres : ResOut C s' f' o (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    ∃ o', RunC P host C s f stk.reverse (.plain (.block bt B) :: code) s' f' o' ∧
      ResOut C s' f' o' (s₁, f₁, fl') := by
  obtain ⟨t₁, t₂, hbt, rfl, rfl⟩ := blockType_of_arity har
  have hin' := Proofs.Region.run_vals (vs := []) (by simpa using hin)
  obtain ⟨o', hr, hres'⟩ := label_abrupt (ws := (stk.drop t₁.length).reverse) (n := t₂.length)
    (cont := []) (code := code) hin' hres hfl
  exact ⟨o', by rw [rev_split stk t₁.length]; exact RunC.block hbt (len_rev_take hp) hr, hres'⟩

/-- A loop whose body falls through with `vs`. -/
theorem loop_cont (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hin : RunC P host C s f (stk.take np).reverse (expression B) s' f' o)
    (hres : ResOut C s' f' o (s₁, f₁, .normal vs)) (hl : vs.length = nr)
    (hk : RunC P host C s₁ f₁ (vs.take nr ++ stk.drop np).reverse code s₂ f₂ o₂) :
    RunC P host C s f stk.reverse (.plain (.loop bt B) :: code) s₂ f₂ o₂ := by
  obtain ⟨t₁, t₂, hbt, rfl, rfl⟩ := blockType_of_arity har
  rw [rev_split stk t₁.length]
  refine RunC.loop hbt (len_rev_take hp) ?_
  have hin' := Proofs.Region.run_vals (vs := []) (by simpa using hin)
  obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
  rw [List.reverse_append, List.take_of_length_le (le_of_eq hl)] at hk
  exact .labelNormal hin' hk

/-- A loop whose body branches back to it with `vs`: the loop is entered again. -/
theorem loop_back (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hin : RunC P host C s f (stk.take np).reverse (expression B) s' f' o)
    (hres : ResOut C s' f' o (s₁, f₁, .brk 0 vs)) (hnp : np ≤ vs.length)
    (hk : RunC P host C s₁ f₁ (vs.take np ++ stk.drop np).reverse (.plain (.loop bt B) :: code)
      s₂ f₂ o₂) :
    RunC P host C s f stk.reverse (.plain (.loop bt B) :: code) s₂ f₂ o₂ := by
  obtain ⟨t₁, t₂, hbt, rfl, rfl⟩ := blockType_of_arity har
  rw [rev_split stk t₁.length]
  refine RunC.loop hbt (len_rev_take hp) ?_
  have hin' := Proofs.Region.run_vals (vs := []) (by simpa using hin)
  obtain ⟨rfl, rfl, junk, rfl⟩ := resOut_brk hres
  rw [rev_split vs t₁.length, ← List.append_assoc] at hin'
  rw [List.reverse_append] at hk
  have hk' := Proofs.Region.run_vals hk
  exact .labelBr0 hin' (len_rev_take hnp) (by simpa [expression, List.append_assoc] using hk')

/-- A loop whose body ends abruptly. -/
theorem loop_abrupt {fl' : Flow} (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hin : RunC P host C s f (stk.take np).reverse (expression B) s' f' o)
    (hres : ResOut C s' f' o (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    ∃ o', RunC P host C s f stk.reverse (.plain (.loop bt B) :: code) s' f' o' ∧
      ResOut C s' f' o' (s₁, f₁, fl') := by
  obtain ⟨t₁, t₂, hbt, rfl, rfl⟩ := blockType_of_arity har
  have hin' := Proofs.Region.run_vals (vs := []) (by simpa using hin)
  obtain ⟨o', hr, hres'⟩ := label_abrupt (ws := (stk.drop t₁.length).reverse) (n := t₁.length)
    (cont := [.loop bt B]) (code := code) hin' hres hfl
  exact ⟨o', by rw [rev_split stk t₁.length]; exact RunC.loop hbt (len_rev_take hp) hr, hres'⟩

/-- An `if` on a native condition `cv` runs the chosen arm as a block. -/
theorem if_arm {cv : Val} {b : Bool} {T E : List BExpr} (hb : truthy cv = some b)
    (h : RunC P host C s f stk.reverse
      (.plain (.block bt (BExpr.lowerList (if b then T else E))) :: code) s' f' o) :
    RunC P host C s f (cv :: stk).reverse
      (.plain (.if_ bt (BExpr.lowerList T) (BExpr.lowerList E)) :: code) s' f' o := by
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  simp only [List.reverse_cons]
  refine RunC.if_ ?_
  by_cases h0 : c₀ = 0
  · subst h0; simpa using h
  · have h1 : (c₀ != 0) = true := by simpa using h0
    rw [h1] at h
    split
    · next hc => exact absurd hc h0
    · simpa using h

end Blocks

/-! ## Tail calls -/

section Tails

variable {s : Store H} {f : Frame} {stk : List Val} {code : List Admin}

theorem steps_one_vals {W : List Val} {X Y : List Admin} {s' : Store H} {f' : Frame}
    (h : Step P host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps P host ⟨s, f, vals W ++ X⟩ ⟨s', f', vals W ++ Y⟩ := by
  simpa using Proofs.Region.steps_in (P := P) (host := host) W [] (.single h)

theorem tableGet_val {x : TableIdx} {ad : AddrType} {i : BitVec ad.intType.width} {W : List Val}
    {ta : Nat} {ti : TableInst} {r : Ref} (ht : s.table? f x = some (ta, ti))
    (hr : ti.refs[i.toNat]? = some r) :
    Steps P host ⟨s, f, vals (W ++ [.num ⟨.int ad.intType, i⟩]) ++ [.plain (.tableGet x)]⟩
      ⟨s, f, vals (W ++ [.ref r])⟩ := by
  rw [Proofs.Region.vals_snoc_num, Proofs.Region.vals_snoc_ref, List.append_assoc]
  exact steps_one_vals (Step.table (TableStep.getVal (P := P) (a := ad) (i := i) ht hr))

theorem cast_val {y : TypeIdx} {W : List Val} {r : Ref}
    (hc : RefOk s r (f.module.instRef (Abstract.CallRes.castTo y))) :
    Steps P host ⟨s, f, vals (W ++ [.ref r]) ++ [.plain (.refCast ⟨true, .typeIdx y⟩)]⟩
      ⟨s, f, vals (W ++ [.ref r])⟩ := by
  rw [Proofs.Region.vals_snoc_ref, List.append_assoc]
  exact steps_one_vals (Step.reference (RefStep.castSucceed hc))

/-- **A resolved tail call ends the region in a pending tail call** of its callee, over the
stack under the popped operand. -/
theorem tail_run {i : Instr} {fa : Nat}
    (hres : Abstract.CallX.TailRes s f i stk (some (fa, stk.drop (Abstract.CallX.tailPop i)))) :
    ∃ c, RunC P host C s f stk.reverse (.plain i :: code) s f
      (.tail (stk.drop (Abstract.CallX.tailPop i)).reverse fa c) := by
  generalize ho : (some (fa, stk.drop (Abstract.CallX.tailPop i)) : Option (Nat × List Val)) = p at hres
  cases hres with
  | direct hfi =>
    simp only [Option.some.injEq, Prod.mk.injEq, Abstract.CallX.tailPop, List.drop_zero] at ho
    obtain ⟨rfl, -⟩ := ho
    exact ⟨_, .returnCall hfi⟩
  | @indirect x y ad i' fa' stk' hres' =>
    simp only [Option.some.injEq, Prod.mk.injEq, Abstract.CallX.tailPop, List.drop_succ_cons,
      List.drop_zero] at ho
    obtain ⟨rfl, -⟩ := ho
    cases hres' with
    | func ht hr hc =>
      refine ⟨.plain (.returnCallRef y), ?_⟩
      simp only [Abstract.CallX.tailPop, List.drop_succ_cons, List.drop_zero, List.reverse_cons]
      exact .returnCallIndirect (.simple (by simp [SingleThreaded.Det.famOf]) (tableGet_val ht hr)
        (.simple (by simp [SingleThreaded.Det.famOf]) (cast_val hc) (.returnCallRef trivial)))
  | @ref y fa' stk' =>
    simp only [Option.some.injEq, Prod.mk.injEq, Abstract.CallX.tailPop, List.drop_succ_cons,
      List.drop_zero] at ho
    obtain ⟨rfl, -⟩ := ho
    refine ⟨.plain (.returnCallRef y), ?_⟩
    simp only [Abstract.CallX.tailPop, List.drop_succ_cons, List.drop_zero, List.reverse_cons]
    exact .returnCallRef trivial
  | indirectTrap => cases ho
  | refNull => cases ho

/-- **An unresolved tail call traps**, at once or as a pending tail call of null. -/
theorem tailRes_none_run {i : Instr} (hres : Abstract.CallX.TailRes s f i stk none) :
    ∃ o, RunC P host C s f stk.reverse (.plain i :: code) s f o ∧ FlowRel .trap o ∧
      ∀ W a c, o ≠ .tail W a c := by
  generalize ho : (none : Option (Nat × List Val)) = p at hres
  cases hres with
  | direct => cases ho
  | indirect => cases ho
  | ref => cases ho
  | @indirectTrap x y ad i' stk' hres' =>
    simp only [List.reverse_cons]
    cases hres' with
    | oob ht hl =>
      refine ⟨.trap, .returnCallIndirect (.simpleTrap (by simp [SingleThreaded.Det.famOf]) ?_),
        trivial, by simp⟩
      rw [Proofs.Region.vals_snoc_num, List.append_assoc]
      exact (steps_one_vals (Step.table (TableStep.getOob (P := P) (a := ad) (i := i') ht hl))).trans
        (by simpa using Proofs.Region.steps_trap (P := P) (host := host) s f stk'.reverse [])
    | castFail ht hr hc =>
      refine ⟨.trap, .returnCallIndirect (.simple (by simp [SingleThreaded.Det.famOf])
        (tableGet_val ht hr) (.simpleTrap (by simp [SingleThreaded.Det.famOf]) ?_)), trivial, by simp⟩
      rw [Proofs.Region.vals_snoc_ref, List.append_assoc]
      exact (steps_one_vals (Step.reference (RefStep.castFail hc))).trans
        (by simpa using Proofs.Region.steps_trap (P := P) (host := host) s f stk'.reverse [])
    | null ht hr hc =>
      exact ⟨_, .returnCallIndirect (.simple (by simp [SingleThreaded.Det.famOf]) (tableGet_val ht hr)
        (.simple (by simp [SingleThreaded.Det.famOf]) (cast_val hc) (.returnCallRefNull trivial))),
        trivial, by simp⟩
  | @refNull y stk' =>
    simp only [List.reverse_cons]
    exact ⟨_, .returnCallRefNull trivial, trivial, by simp⟩

end Tails

/-! ## The forward bridge -/

theorem code_op (i : Instr) (args es : List BExpr) :
    expression (BExpr.lowerList (.op i args :: es)) =
      expression (BExpr.lowerList args) ++ .plain i :: expression (BExpr.lowerList es) := by
  simp [expression, BExpr.lowerList, BExpr.lower]

theorem code_block (bt : BlockType) (body es : List BExpr) :
    expression (BExpr.lowerList (.block bt body :: es)) =
      .plain (.block bt (BExpr.lowerList body)) :: expression (BExpr.lowerList es) := by
  simp [expression, BExpr.lowerList, BExpr.lower]

theorem code_loop (bt : BlockType) (body es : List BExpr) :
    expression (BExpr.lowerList (.loop bt body :: es)) =
      .plain (.loop bt (BExpr.lowerList body)) :: expression (BExpr.lowerList es) := by
  simp [expression, BExpr.lowerList, BExpr.lower]

theorem code_if (bt : BlockType) (c t e es : List BExpr) :
    expression (BExpr.lowerList (.if_ bt c t e :: es)) = expression (BExpr.lowerList c) ++
      .plain (.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)) :: expression (BExpr.lowerList es) := by
  simp [expression, BExpr.lowerList, BExpr.lower]

/-- The statement of the forward bridge for one native run. -/
def Fwd (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (s : Store H) (f : Frame)
    (stk : List Val) (es : List BExpr) (r : Store H × Frame × Flow) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChkE tExt s.funcs →
    chkE tExt s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    ∃ s' f' o, RunC P host C s f stk.reverse (expression (BExpr.lowerList es)) s' f' o ∧
      ResOut C s' f' o r

theorem out_normal_of_rel {o : Region.Out} {vs : List Val} (h : FlowRel (.normal vs) o) :
    o = .normal vs.reverse := by
  cases o <;> simp_all [FlowRel]

theorem not_normal_of_rel {o : Region.Out} {fl : Flow} (h : FlowRel fl o) (hfl : ¬ fl.IsNormal) :
    ∀ us, o ≠ .normal us := by
  rintro us rfl; cases fl <;> simp_all [FlowRel, Flow.IsNormal]

theorem abrupt_cases {fl : Flow} (h : fl.Abrupt) : fl = .trap ∨ ∃ t, fl = .throw t := by
  cases fl <;> simp_all [Flow.Abrupt]

variable {P₀ : Profile} {host₀ : HostSemantics H}

theorem arityG (hC : OracleSoundT P₀ host₀ C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : Abstract.CallXT.EvalOXT C s f stk es r) :
    ArityGoodE tExt s f stk es r :=
  (evalOXT_goodT hC h).1

theorem fwd (hC : OracleSoundT P₀ host₀ C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : Abstract.CallXT.EvalOXT C s f stk es r) :
    Fwd P host C s f stk es r := by
  induction h with
  | nil =>
    intro labels ret out hS hchk
    refine ⟨_, _, .normal _, by simpa [expression] using (RunC.nil : RunC P host C _ _ _ [] _ _ _), ?_⟩
    exact ⟨rfl, rfl, by simp [FlowRel]⟩
  | argsAbort hargs hfl iha =>
    intro labels ret out hS hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres⟩ := iha hS ha
    exact ⟨s', f', o, by
      rw [code_op]; exact Proofs.Region.run_append hr (thenC_stop (resOut_not_normal hres hfl)), hres⟩
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r hargs hfi hty hcall hvs hk iha ihk =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS hA hfi hty hchk
    obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ := oracle_at hC.soundE hS inv1 hfi hty hp hcall f₁
    have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    have inv2 : EvalInvE tExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
      ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
    have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
        stk₁.length - ps.length + rs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have h2' : chkE tExt s₂.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
      rw [hlen]; exact chk_inv inv2 h2
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    obtain ⟨s'', f'', o'', hr'', hres''⟩ := ihk (storeChk_inv inv2 hS) h2'
    refine ⟨s'', f'', o'', ?_, hres''⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [rev_split stk₁ ps.length]
    exact RunC.call hfi hty (len_rev_take hp) hcall hvs (by simpa [List.reverse_append] using hr'')
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty hcall iha =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨-, hp, -⟩ := arity_call_pre hS hA hfi hty hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    refine ⟨s₂, _, .trap, ?_, rfl, rfl, trivial⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [rev_split stk₁ ps.length]
    exact RunC.callTrap hfi hty (len_rev_take hp) hcall
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t hargs hfi hty hcall iha =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨-, hp, -⟩ := arity_call_pre hS hA hfi hty hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    refine ⟨s₂, _, .throw t, ?_, rfl, rfl, rfl⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [rev_split stk₁ ps.length]
    exact RunC.callThrow hfi hty (len_rev_take hp) hcall
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi hargs hflat hk iha ihk =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨o₀, h1, h2⟩ := chk_consE.mp hchk
    obtain ⟨hf, inv1⟩ := arity_args hS hA h1
    replace hf := flatChk_of_evalFlat hflat hf
    obtain ⟨ho, inv2⟩ := flat_normal (ext := tExt) hflat hf
    have inv12 := inv1.trans inv2
    have h2' : chkE tExt s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact chk_inv inv12 h2
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    obtain ⟨o', hr', hrel, -⟩ := flat_run (P := P) (host := host) (C := C) hi hf hflat
    obtain rfl := out_normal_of_rel hrel
    obtain ⟨s'', f'', o'', hr'', hres''⟩ := ihk (storeChk_inv inv12 hS) h2'
    refine ⟨s'', f'', o'', ?_, hres''⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [← List.singleton_append]
    exact Proofs.Region.run_append hr' (by simp only [ThenC]; exact hr'')
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi hargs hflat hfl iha =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨hf, -⟩ := arity_args hS hA h1
    replace hf := flatChk_of_evalFlat hflat hf
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    obtain ⟨o', hr', hrel, hnt⟩ := flat_run (P := P) (host := host) (C := C) hi hf hflat
    refine ⟨s₂, f₂, o', ?_, resOut_of_rel hnt hrel⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [← List.singleton_append]
    exact Proofs.Region.run_append hr' (thenC_stop (not_normal_of_rel hrel hfl))
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har hbody hvs hk ihb ihk =>
    intro labels ret out hS hchk
    obtain ⟨hp, hb, h2⟩ := arity_block_pre har hchk
    have hB : ArityGoodE tExt _ _ _ _ _ := arityG hC hbody
    obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hB hb (take_length_of_le hp)
    have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact length_of_ends hok hob
    obtain ⟨s', f', o, hr, hres⟩ := ihb hS hbc
    obtain ⟨s'', f'', o'', hr'', hres''⟩ := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
    exact ⟨s'', f'', o'', by rw [code_block]; exact block_cont har hp hr hres hvs hnr hnorm hr'',
      hres''⟩
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ihb =>
    intro labels ret out hS hchk
    obtain ⟨hp, hb, -⟩ := arity_block_pre har hchk
    have hB : ArityGoodE tExt _ _ _ _ _ := arityG hC hbody
    obtain ⟨ob, hob, hbc, -⟩ := body_facts hS hB hb (take_length_of_le hp)
    obtain ⟨s', f', o, hr, hres⟩ := ihb hS hbc
    obtain ⟨o', hr', hres'⟩ := block_abrupt (code := expression (BExpr.lowerList es)) har hp hr hres
      (.inl ⟨_, _, rfl, rfl⟩)
    exact ⟨s', f', o', by rw [code_block]; exact hr', hres'⟩
  | @blockEsc s s₁ f f₁ stk bt body es np nr fl har hbody hfl ihb =>
    intro labels ret out hS hchk
    obtain ⟨hp, hb, -⟩ := arity_block_pre har hchk
    have hB : ArityGoodE tExt _ _ _ _ _ := arityG hC hbody
    obtain ⟨ob, hob, hbc, -⟩ := body_facts hS hB hb (take_length_of_le hp)
    obtain ⟨s', f', o, hr, hres⟩ := ihb hS hbc
    obtain ⟨o', hr', hres'⟩ := block_abrupt (code := expression (BExpr.lowerList es)) har hp hr hres
      (.inr ⟨hfl, rfl⟩)
    exact ⟨s', f', o', by rw [code_block]; exact hr', hres'⟩
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har hbody hk ihb ihk =>
    intro labels ret out hS hchk
    obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hchk
    have hB : ArityGoodE tExt _ _ _ _ _ := arityG hC hbody
    obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hB hb (take_length_of_le hp)
    have hlen : vs.length = nr := length_of_ends hok hob
    obtain ⟨s', f', o, hr, hres⟩ := ihb hS hbc
    obtain ⟨s'', f'', o'', hr'', hres''⟩ :=
      ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hlen.ge h2)
    exact ⟨s'', f'', o'', by rw [code_loop]; exact loop_cont har hp hr hres hlen hr'', hres''⟩
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har hbody hk ihb ihk =>
    intro labels ret out hS hchk
    obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
    have hB : ArityGoodE tExt _ _ _ _ _ := arityG hC hbody
    obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hB hb (take_length_of_le hp)
    obtain ⟨m, hm, hle⟩ := hok
    have hnp : np ≤ vs.length := by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      exact hm ▸ hle
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have hc' : chkE tExt s₁.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
      rw [hlen]; exact chk_inv inv1 hchk
    obtain ⟨s', f', o, hr, hres⟩ := ihb hS hbc
    obtain ⟨s'', f'', o'', hr'', hres''⟩ := ihk (storeChk_inv inv1 hS) hc'
    rw [code_loop] at hr''
    exact ⟨s'', f'', o'', by rw [code_loop]; exact loop_back har hp hr hres hnp hr'', hres''⟩
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ihb =>
    intro labels ret out hS hchk
    obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
    have hB : ArityGoodE tExt _ _ _ _ _ := arityG hC hbody
    obtain ⟨ob, hob, hbc, -⟩ := body_facts hS hB hb (take_length_of_le hp)
    obtain ⟨s', f', o, hr, hres⟩ := ihb hS hbc
    obtain ⟨o', hr', hres'⟩ := loop_abrupt (code := expression (BExpr.lowerList es)) har hp hr hres
      (.inl ⟨_, _, rfl, rfl⟩)
    exact ⟨s', f', o', by rw [code_loop]; exact hr', hres'⟩
  | @loopEsc s s₁ f f₁ stk bt body es np nr fl har hbody hfl ihb =>
    intro labels ret out hS hchk
    obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
    have hB : ArityGoodE tExt _ _ _ _ _ := arityG hC hbody
    obtain ⟨ob, hob, hbc, -⟩ := body_facts hS hB hb (take_length_of_le hp)
    obtain ⟨s', f', o, hr, hres⟩ := ihb hS hbc
    obtain ⟨o', hr', hres'⟩ := loop_abrupt (code := expression (BExpr.lowerList es)) har hp hr hres
      (.inr ⟨hfl, rfl⟩)
    exact ⟨s', f', o', by rw [code_loop]; exact hr', hres'⟩
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c tt el es np nr fl r hc hb har harm hvs hk ihc iharm
      ihk =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hc
    have hM : ArityGoodE tExt _ _ _ _ _ := arityG hC harm
    obtain ⟨oc, ob, hco, hbc, hob, hok, inv1, inv2, hp, h2⟩ := if_facts hS hA har hM hchk
    have hS1 : StoreChkE tExt s₁.funcs := storeChk_inv inv1 hS
    have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact length_of_ends hok hob
    obtain ⟨s', f', o, hr, hres⟩ := ihc hS hco
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    obtain ⟨sa, fa', oa, hra, hresa⟩ := iharm hS1 hbc
    obtain ⟨s'', f'', o'', hr'', hres''⟩ := ihk (storeChk_inv inv2 hS1) (chk_after inv2 hp hnr h2)
    refine ⟨s'', f'', o'', ?_, hres''⟩
    rw [code_if]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    exact if_arm hb (block_cont har hp hra hresa hvs hnr hnorm hr'')
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c tt el es np nr k hc hb har harm ihc iharm =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hc
    have hM : ArityGoodE tExt _ _ _ _ _ := arityG hC harm
    obtain ⟨oc, ob, hco, hbc, -, -, inv1, -, hp, -⟩ := if_facts hS hA har hM hchk
    obtain ⟨s', f', o, hr, hres⟩ := ihc hS hco
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    obtain ⟨sa, fa', oa, hra, hresa⟩ := iharm (storeChk_inv inv1 hS) hbc
    obtain ⟨o', hr', hres'⟩ := block_abrupt (code := expression (BExpr.lowerList es)) har hp hra
      hresa (.inl ⟨_, _, rfl, rfl⟩)
    refine ⟨sa, fa', o', ?_, hres'⟩
    rw [code_if]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    exact if_arm hb hr'
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c tt el es np nr fl hc hb har harm hfl ihc iharm =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hc
    have hM : ArityGoodE tExt _ _ _ _ _ := arityG hC harm
    obtain ⟨oc, ob, hco, hbc, -, -, inv1, -, hp, -⟩ := if_facts hS hA har hM hchk
    obtain ⟨s', f', o, hr, hres⟩ := ihc hS hco
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres
    obtain ⟨sa, fa', oa, hra, hresa⟩ := iharm (storeChk_inv inv1 hS) hbc
    obtain ⟨o', hr', hres'⟩ := block_abrupt (code := expression (BExpr.lowerList es)) har hp hra
      hresa (.inr ⟨hfl, rfl⟩)
    refine ⟨sa, fa', o', ?_, hres'⟩
    rw [code_if]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    exact if_arm hb hr'
  | ifAbort hc hfl ihc =>
    intro labels ret out hS hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oc, hco, -⟩ := chk1_ifE h1
    obtain ⟨s', f', o, hr, hres⟩ := ihc hS hco
    exact ⟨s', f', o, by
      rw [code_if]; exact Proofs.Region.run_append hr (thenC_stop (resOut_not_normal hres hfl)), hres⟩
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r hargs hres hfi hty hy hcall hvs hk iha ihk =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨inv1, hp, h2⟩ := arity_ir_preT hS hA (.inl ⟨x, rfl⟩) hy hchk
    obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ :=
      oracleX_atT hC hS inv1 hfi hty hp hcall f₁ (c := .plain (.callRef y)) trivial
    have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    have inv2 : EvalInvE tExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
      ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
    have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
        stk₁.length - ps.length + rs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have h2' : chkE tExt s₂.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
      rw [hlen]; exact chk_inv inv2 h2
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres0⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres0
    obtain ⟨s'', f'', o'', hr'', hres''⟩ := ihk (storeChk_inv inv2 hS) h2'
    refine ⟨s'', f'', o'', ?_, hres''⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [List.reverse_cons, rev_split stk₁ ps.length]
    exact RunC.callInd hres hfi hty (len_rev_take hp) hcall hvs (by simpa [List.reverse_append] using hr'')
  | @callIndRes s s₁ f f₁ stk stk₁ x y args es ad i hargs hres iha =>
    intro labels ret out hS hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres'⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres'
    refine ⟨_, _, .trap, ?_, rfl, rfl, trivial⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [List.reverse_cons]
    exact RunC.callIndRes hres
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl hargs hres hfi hty hy hcall hfl iha =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨-, hp, -⟩ := arity_ir_preT hS hA (.inl ⟨x, rfl⟩) hy hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres0⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres0
    rcases abrupt_cases hfl with rfl | ⟨t, rfl⟩
    · refine ⟨s₂, _, .trap, ?_, rfl, rfl, trivial⟩
      rw [code_op]
      refine Proofs.Region.run_append hr ?_
      simp only [ThenC]
      rw [List.reverse_cons, rev_split stk₁ ps.length]
      exact RunC.callIndTrap hres hfi hty (len_rev_take hp) hcall
    · refine ⟨s₂, _, .throw t, ?_, rfl, rfl, rfl⟩
      rw [code_op]
      refine Proofs.Region.run_append hr ?_
      simp only [ThenC]
      rw [List.reverse_cons, rev_split stk₁ ps.length]
      exact RunC.callIndThrow hres hfi hty (len_rev_take hp) hcall
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r hargs hfi hty hy hcall hvs hk iha ihk =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨inv1, hp, h2⟩ := arity_ir_preT hS hA (.inr rfl) hy hchk
    obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ :=
      oracleX_atT hC hS inv1 hfi hty hp hcall f₁ (c := .plain (.callRef y)) trivial
    have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    have inv2 : EvalInvE tExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
      ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
    have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
        stk₁.length - ps.length + rs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have h2' : chkE tExt s₂.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
      rw [hlen]; exact chk_inv inv2 h2
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres0⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres0
    obtain ⟨s'', f'', o'', hr'', hres''⟩ := ihk (storeChk_inv inv2 hS) h2'
    refine ⟨s'', f'', o'', ?_, hres''⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [List.reverse_cons, rev_split stk₁ ps.length]
    exact RunC.callRef hfi hty (len_rev_take hp) hcall hvs (by simpa [List.reverse_append] using hr'')
  | @callRefNull s s₁ f f₁ stk stk₁ y args es hargs iha =>
    intro labels ret out hS hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres'⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres'
    refine ⟨_, _, .trap, ?_, rfl, rfl, trivial⟩
    rw [code_op]
    refine Proofs.Region.run_append hr ?_
    simp only [ThenC]
    rw [List.reverse_cons]
    exact RunC.callRefNull
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl hargs hfi hty hy hcall hfl iha =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨-, hp, -⟩ := arity_ir_preT hS hA (.inr rfl) hy hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres0⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres0
    rcases abrupt_cases hfl with rfl | ⟨t, rfl⟩
    · refine ⟨s₂, _, .trap, ?_, rfl, rfl, trivial⟩
      rw [code_op]
      refine Proofs.Region.run_append hr ?_
      simp only [ThenC]
      rw [List.reverse_cons, rev_split stk₁ ps.length]
      exact RunC.callRefTrap hfi hty (len_rev_take hp) hcall
    · refine ⟨s₂, _, .throw t, ?_, rfl, rfl, rfl⟩
      rw [code_op]
      refine Proofs.Region.run_append hr ?_
      simp only [ThenC]
      rw [List.reverse_cons, rev_split stk₁ ps.length]
      exact RunC.callRefThrow hfi hty (len_rev_take hp) hcall
  | @tail s s₁ s₂ f f₁ stk stk₁ i args es fa fi ps rs fl hargs hres hfi hty hy hcall hfl iha =>
    intro labels ret out hS hchk
    have hA : ArityGoodE tExt _ _ _ _ _ := arityG hC hargs
    obtain ⟨-, hp, -⟩ := tail_preT hS hA hres hfi hty hy hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres'⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres'
    obtain ⟨c, hrt⟩ := tail_run (P := P) (host := host) (C := C)
      (code := expression (BExpr.lowerList es)) hres
    have hp' : ps.length ≤ (stk₁.drop (Abstract.CallX.tailPop i)).length := by
      simp only [List.length_drop]; omega
    refine ⟨_, _, .tail _ fa c, ?_, fi, ps, rs,
      ((stk₁.drop (Abstract.CallX.tailPop i)).drop ps.length).reverse,
      ((stk₁.drop (Abstract.CallX.tailPop i)).take ps.length).reverse, fl, hfi, hty,
      rev_split _ _, len_rev_take hp', hcall, hfl, rfl, rfl⟩
    rw [code_op]
    exact Proofs.Region.run_append hr (by simp only [ThenC]; exact hrt)
  | @tailRes s s₁ f f₁ stk stk₁ i args es hargs hres iha =>
    intro labels ret out hS hchk
    obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨s', f', o, hr, hres'⟩ := iha hS ha
    obtain ⟨rfl, rfl, rfl⟩ := resOut_normal hres'
    obtain ⟨o', hr', hrel, hnt⟩ := tailRes_none_run (P := P) (host := host) (C := C)
      (code := expression (BExpr.lowerList es)) hres
    refine ⟨_, _, o', ?_, resOut_of_rel hnt hrel⟩
    rw [code_op]
    exact Proofs.Region.run_append hr (by simp only [ThenC]; exact hr')

/-! ## The typed closed extended oracle -/

theorem oracleSoundT_closedXOk (P : Profile) :
    OracleSoundT P noHostX (Machine.closedXOk (H := H)) :=
  fun s s₂ f a fi ps rs us fl c hS hfi hty hn hc hcall =>
    Interp.OracleX.oracleSoundT_typedClosed (P := P) s s₂ f a fi ps rs us fl c hS hfi hty hn hc
      hcall.2

theorem keepsTy_closedXOk : Abstract.CallXT.KeepsTy (Machine.closedXOk (H := H)) :=
  fun s a args out h hs => Abstract.CallXT.closedCallX_keepsTy s a args out h.2.2 hs

end Silmaril.Wasm.Cfg.Proofs.Bridge
