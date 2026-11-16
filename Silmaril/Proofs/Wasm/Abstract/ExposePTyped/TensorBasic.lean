module

public import Silmaril.Wasm.Abstract.ExposePTyped.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePTyped.Thms`: the stack tensor on body results
(`whiskO`, `trimO`, `GoodO`) and on flat instructions, and the stack facts of tail calls.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP

variable {H : Type}

/-! ## Body results -/

theorem whiskO_abrupt {rest : List Val} {o : POut} (h : ¬ o.IsNormal) : whiskO rest o = o := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    first | rfl | exact absurd trivial h

theorem notNormal_of_escapes {o : POut} (h : o.Escapes) : ¬ o.IsNormal := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    simp_all [POut.Escapes, POut.IsNormal, Flow.Escapes, Flow.IsNormal]

theorem notNormal_of_abrupt {fl : Flow} (h : fl.Abrupt) : ¬ (POut.flow fl).IsNormal := by
  rcases fl with _ | _ | _ | _ | _ <;> simp_all [POut.IsNormal, Flow.IsNormal, Flow.Abrupt]

theorem trimO_normal_iff {L : List Nat} {r : Nat} {o : POut} {vs : List Val} :
    trimO L r o = .flow (.normal vs) ↔ o = .flow (.normal vs) := by
  rcases o with (ws | ⟨l, ws⟩ | ws | _ | a) | ⟨a, args, n⟩ <;> simp [trimO]

theorem trimO_abrupt {L : List Nat} {r : Nat} {o : POut} (h : ¬ o.IsNormal) :
    ¬ (trimO L r o).IsNormal := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    simp_all [trimO, POut.IsNormal, Flow.IsNormal]

/-- A run read through `trimO` as a whiskered fallthrough is that fallthrough. -/
theorem eq_of_trim_normal {L : List Nat} {r : Nat} {o : POut} {rest vs : List Val}
    (h : trimO L r o = trimO L r (whiskO rest (.flow (.normal vs)))) :
    o = .flow (.normal (vs ++ rest)) :=
  trimO_normal_iff.mp h

theorem notNormal_of_trim {L : List Nat} {r : Nat} {o o' : POut} (ho : ¬ o.IsNormal)
    (h : trimO L r o' = trimO L r o) : ¬ o'.IsNormal := by
  intro hn
  rcases o' with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    simp only [POut.IsNormal, Flow.IsNormal] at hn
  have := trimO_abrupt (L := L) (r := r) ho
  rw [← h] at this
  exact this trivial

theorem goodO_abrupt {L : List Nat} {r : Nat} {o : POut} {oa oc : Option Nat}
    (ho : ¬ o.IsNormal) (h : GoodO L r oa o) : GoodO L r oc o := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    first | exact h | exact absurd trivial ho

theorem goodO_brk_succ {L : List Nat} {r n k : Nat} {ob oc : Option Nat} {vs : List Val}
    (h : GoodO (n :: L) r ob (.flow (.brk (k + 1) vs))) : GoodO L r oc (.flow (.brk k vs)) := h

theorem goodO_escape {L : List Nat} {r n : Nat} {ob oc : Option Nat} {o : POut}
    (h : GoodO (n :: L) r ob o) (he : o.Escapes) : GoodO L r oc o := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    trivial

theorem goodO_blockVals {L : List Nat} {r n : Nat} {ob : Option Nat} {fl : Flow} {vs : List Val}
    (h : GoodO (n :: L) r ob (.flow fl)) (he : ob = none ∨ ob = some n)
    (hvs : fl.blockVals = some vs) : n ≤ vs.length := by
  rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | a <;>
    simp only [Flow.blockVals, reduceCtorEq, Option.some.injEq] at hvs
  · subst hvs
    have hv : ob = some ws.length := h
    rcases he with rfl | rfl
    · cases hv
    · exact (Option.some.inj hv).le
  · subst hvs
    obtain ⟨m, hm, hle⟩ := h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle

theorem goodO_normal {L : List Nat} {r n : Nat} {ob : Option Nat} {vs : List Val}
    (h : GoodO L r ob (.flow (.normal vs))) (he : ob = none ∨ ob = some n) : vs.length = n := by
  have hv : ob = some vs.length := h
  rcases he with rfl | rfl
  · cases hv
  · exact (Option.some.inj hv).symm

theorem goodO_of_flowOk {L : List Nat} {r : Nat} {o : Option Nat} {fl : Flow}
    (h : FlowOk L r o fl) : GoodO L r o (.flow fl) := by
  rcases fl with ws | ⟨l, ws⟩ | ws | _ | a <;> first | exact h | trivial

theorem trimO_brk_append {L : List Nat} {r : Nat} {l : Nat} {vs rest : List Val}
    (h : ∃ n, L[l]? = some n ∧ n ≤ vs.length) :
    trimO L r (.flow (.brk l (vs ++ rest))) = trimO L r (.flow (.brk l vs)) := by
  obtain ⟨n, hn, hle⟩ := h
  simp [trimO, hn, List.take_append_of_le_length hle]

/-! ## Flat instructions -/

/-- Append `rest` to every stack a flow carries. -/
def wFl (rest : List Val) : Flow → Flow
  | .normal vs => .normal (vs ++ rest)
  | .brk l vs => .brk l (vs ++ rest)
  | .ret vs => .ret (vs ++ rest)
  | fl => fl

/-- `wFl` on an interpreter outcome. -/
def wE (rest : List Val) (t : Store H × Frame × Flow) : Store H × Frame × Flow :=
  (t.1, t.2.1, wFl rest t.2.2)

theorem stackPure_of_evalFlat {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {r : Store H × Frame × Flow} (h : evalFlat s f stk i = some r) : instrStackPure i = true := by
  cases i <;> first | rfl | (simp [evalFlat] at h)

set_option maxHeartbeats 1000000 in
theorem evalFlat_whisk {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {o : Option Nat}
    (hp : instrStackPure i = true) (hc : flatChkE ext F mi nl ret labels stk.length i = some o)
    (rest : List Val) :
    evalFlat s f (stk ++ rest) i = (evalFlat s f stk i).map (wE rest) := by
  cases i <;> simp only [instrStackPure, Bool.false_eq_true] at hp <;>
    (try cases ‹Option (PackSize × Signedness)›) <;>
    simp only [flatChkE, flatEff] at hc <;>
    rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
    simp [evalFlat, wE, wFl, Option.map_map, Function.comp_def] at hc ⊢
  all_goals first
    | ((repeat' split at hc) <;> simp_all; done)
    | (rcases truthy a with _ | (_ | _) <;> simp; done)
    | (congr 1; funext x; congr 1; funext y; split <;> rfl)
    | ((repeat' split) <;> simp_all [wE, wFl])

theorem notNormal_wFl {rest : List Val} {fl : Flow} (h : ¬ fl.IsNormal) :
    ¬ (wFl rest fl).IsNormal := by
  rcases fl with ws | ⟨l, ws⟩ | ws | _ | a <;> simp_all [wFl, Flow.IsNormal]

theorem trimO_wFl {L : List Nat} {r : Nat} {o : Option Nat} {fl : Flow} {rest : List Val}
    (h : FlowOk L r o fl) :
    trimO L r (.flow (wFl rest fl)) = trimO L r (whiskO rest (.flow fl)) := by
  rcases fl with ws | ⟨l, ws⟩ | ws | _ | a
  · rfl
  · exact trimO_brk_append h
  · have h' : r ≤ ws.length := h
    simp [trimO, wFl, whiskO, List.take_append_of_le_length h']
  · rfl
  · rfl

/-! ## Tail calls -/

theorem tailRes_append {s : Store H} {f : Frame} {i : Instr} {stk rest stk' : List Val} {fa : Nat}
    (h : TailRes s f i stk (some (fa, stk'))) : TailRes s f i (stk ++ rest) (some (fa, stk' ++ rest)) := by
  generalize hp : (some (fa, stk') : Option (Nat × List Val)) = p at h
  cases h with
  | direct hfi => cases hp; exact .direct hfi
  | indirect hres => cases hp; exact .indirect hres
  | ref => cases hp; exact .ref
  | indirectTrap => cases hp
  | refNull => cases hp

theorem tailRes_append_none {s : Store H} {f : Frame} {i : Instr} {stk rest : List Val}
    (h : TailRes s f i stk none) : TailRes s f i (stk ++ rest) none := by
  generalize hp : (none : Option (Nat × List Val)) = p at h
  cases h with
  | direct => cases hp
  | indirect => cases hp
  | ref => cases hp
  | indirectTrap hres => exact .indirectTrap hres
  | refNull => exact .refNull

theorem tailRes_pop {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {p : Option (Nat × List Val)} (h : TailRes s f i stk p) : tailPop i ≤ stk.length := by
  cases h <;> simp [tailPop]

theorem flatChkE_eh_tail {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {k : Nat} {s : Store H} {f : Frame} {i : Instr}
    {stk : List Val} {p : Option (Nat × List Val)} (h : TailRes s f i stk p) :
    flatChkE (ehExt tags) F mi nl ret labels k i = flatChkE tExt F mi nl ret labels k i := by
  cases h <;> rfl

/-! ## Checks along a run -/

theorem chk_eq {ext : ExtArity H} {s s₁ : Store H} {f f₁ : Frame} (hs : s₁.funcs = s.funcs)
    (hm : f₁.module = f.module) (hl : f₁.locals.length = f.locals.length) :
    chkE ext s₁.funcs f₁.module f₁.locals.length = chkE ext s.funcs f.module f.locals.length := by
  rw [hs, hm, hl]

theorem flatChkE_eq {ext : ExtArity H} {s s₁ : Store H} {f f₁ : Frame} (hs : s₁.funcs = s.funcs)
    (hm : f₁.module = f.module) (hl : f₁.locals.length = f.locals.length) :
    flatChkE ext s₁.funcs f₁.module f₁.locals.length =
      flatChkE ext s.funcs f.module f.locals.length := by
  rw [hs, hm, hl]

theorem good_funcs {Γ : Ctx H} {s s₁ : Store H} (hg : Γ.Good s) (hg₁ : Γ.Good s₁) :
    s₁.funcs = s.funcs := hg₁.1.trans hg.1.symm

end Silmaril.Proofs.Wasm.Abstract.ExposePTyped
