module

public import Silmaril.Wasm.Abstract.ExposePTyped.Defs
public import Silmaril.Wasm.Abstract.ExposePStruct.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePTyped.Thms`: typed code (`TMor`) is closed under the
identity, composition, the structured instructions, the call forms, the tail calls and the
exception operators, it forgets to #529's checked code, and the image of the denotation is
closed under the operations on bodies.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXT (typeArity)
open Silmaril.Wasm.Abstract.ExposeP (ResP)

variable {H : Type} {Γ : Ctx H}

/-! ## Interfaces -/

theorem env_eq {I J : TIface} {xs : List Nat} (hm : J.mi = I.mi) (hC : J.C = I.C.initLocals xs) :
    J.env = I.env := by
  simp only [TIface.env, hm, hC, Context.initLocals_labels, Context.initLocals_return,
    Context.initLocals_locals_length]

theorem forget_withLabel (mi : ModuleInst) (C : Context) (L ts : List CValType) :
    (TIface.mk mi (C.withLabel L) ts).forget =
      ⟨(TIface.mk mi C ts).env.push L.length, ts.length⟩ := rfl

theorem forget_withLabel_of {I : TIface} {C : Context} {xs : List Nat} (hC : C = I.C.initLocals xs)
    (L ts : List CValType) :
    (TIface.mk I.mi (C.withLabel L) ts).forget = ⟨I.env.push L.length, ts.length⟩ := by
  rw [forget_withLabel, env_eq (I := I) (J := ⟨I.mi, C, ts⟩) rfl hC]

theorem inBounds_append {C : Context} {xs₁ xs₂ : List Nat}
    (h₁ : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
    (h₂ : ∀ x ∈ xs₂, ∃ lt, (C.initLocals xs₁).locals[x]? = some lt) :
    ∀ x ∈ xs₁ ++ xs₂, ∃ lt, C.locals[x]? = some lt := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact h₁ x h
  · obtain ⟨lt, hlt⟩ := h₂ x h
    rw [Context.initLocals_locals] at hlt
    split at hlt
    · obtain ⟨lt', h', -⟩ := Option.map_eq_some_iff.1 hlt
      exact ⟨lt', h'⟩
    · exact ⟨lt, hlt⟩

theorem types_initLocals (C : Context) (xs : List Nat) : (C.initLocals xs).types = C.types :=
  congrArg TypeCtx.types (Context.initLocals_toTypeCtx C xs)

theorem blockArity_of_ok {mi : ModuleInst} {C : Context} (ht : C.types = mi.types) {bt : BlockType}
    {t₁ t₂ : List CValType} (h : BlockTypeOk C bt t₁ t₂) :
    blockArity mi bt = some (t₁.length, t₂.length) := by
  obtain ⟨t₁', t₂', hb, h₁, h₂⟩ := blockType_of_types (f := { module := mi }) ht h
  cases bt <;> simp_all [blockArity, Binaryen.arity, ModuleInst.blockType?, Frame.type?]
  obtain ⟨-, rfl⟩ := hb
  simpa using h₂

theorem ftOut_endsAt (ft : Bool) (n : Nat) : endsAt (some (ftOut ft n)) n = true := by
  cases ft <;> simp [ftOut, endsAt]

/-! ## The category -/

theorem thom_id {I : TIface} (hI : I.Ok) : THom Γ I I [] := by
  refine ⟨rfl, [], by simp, by simp, ?_, mor_id I.forget⟩
  simpa using InstrsOk.frame (ts := I.ts) (InstrsOk.nil (C := I.C)) hI

theorem tmor_comp {I J K : TIface} {ft : Bool} {es₁ es₂ : List BExpr} (h₁ : THom Γ I J es₁)
    (h₂ : TMor Γ J K ft es₂) : TMor Γ I K ft (es₁ ++ es₂) := by
  obtain ⟨hm₁, xs₁, hx₁, hC₁, ht₁, hc₁⟩ := h₁
  obtain ⟨hm₂, xs₂, hx₂, hC₂, ht₂, hc₂⟩ := h₂
  rw [hC₁] at hx₂ ht₂
  refine ⟨hm₂.trans hm₁, xs₁ ++ xs₂, inBounds_append hx₁ hx₂, ?_, ?_, ?_⟩
  · rw [hC₂, hC₁, Context.initLocals_append]
  · rw [BExpr.lowerList_append]; exact InstrsOk.seq ht₁ hx₁ ht₂
  · have e : J.forget = ⟨I.forget.env, J.ts.length⟩ := by
      simp only [TIface.forget, env_eq hm₁ hC₁]
    rw [e] at hc₂
    exact mor_comp hc₁ hc₂

theorem tmor_stop {I J K : TIface} {ft : Bool} {es₁ es₂ : List BExpr} (h₁ : TStop Γ I J es₁)
    (h₂ : TMor Γ J K ft es₂) : TStop Γ I K (es₁ ++ es₂) := by
  obtain ⟨hm₁, xs₁, hx₁, hC₁, ht₁, hc₁⟩ := h₁
  obtain ⟨hm₂, xs₂, hx₂, hC₂, ht₂, -⟩ := h₂
  rw [hC₁] at hx₂ ht₂
  refine ⟨hm₂.trans hm₁, xs₁ ++ xs₂, inBounds_append hx₁ hx₂, ?_, ?_, mor_stop hc₁ es₂⟩
  · rw [hC₂, hC₁, Context.initLocals_append]
  · rw [BExpr.lowerList_append]; exact InstrsOk.seq ht₁ hx₁ ht₂

/-! ## Structured instructions -/

theorem thom_block {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.block bt body] := by
  obtain ⟨-, xs, -, -, hbc, hbm⟩ := hb
  rw [hJ] at hbc hbm
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts]
    simpa [BExpr.lower] using InstrsOk.frame (InstrsOk.instr (InstrOk.block hbt hbc)) hpre
  · have e : I.ts.length - t₁.length + t₂.length = (pre ++ t₂).length := by
      rw [hts]; simp
    show Mor Γ I.forget (some _) _
    rw [← e]
    exact mor_block (I := I.forget) (blockArity_of_ok hty hbt) (by simp [TIface.forget, hts])
      hbm (ftOut_endsAt ft _)

theorem thom_loop {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₁, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.loop bt body] := by
  obtain ⟨-, xs, -, -, hbc, hbm⟩ := hb
  rw [hJ] at hbc hbm
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts]
    simpa [BExpr.lower] using InstrsOk.frame (InstrsOk.instr (InstrOk.loop hbt hbc)) hpre
  · have e : I.ts.length - t₁.length + t₂.length = (pre ++ t₂).length := by
      rw [hts]; simp
    show Mor Γ I.forget (some _) _
    rw [← e]
    exact mor_loop (I := I.forget) (blockArity_of_ok hty hbt) (by simp [TIface.forget, hts])
      hbm (ftOut_endsAt ft _)

theorem thom_if {I K J₁ J₂ : TIface} {bt : BlockType} {c t el : List BExpr}
    {pre t₁ t₂ : List CValType} {ft₁ ft₂ : Bool} (hc : THom Γ I K c)
    (hty : I.C.types = I.mi.types) (hts : K.ts = pre ++ t₁ ++ [.i32])
    (hpre : ResultOk K.C.toTypeCtx pre) (hbt : BlockTypeOk K.C bt t₁ t₂)
    (ht : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₁ ft₁ t) (hJ₁ : J₁.ts = t₂)
    (he : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₂ ft₂ el) (hJ₂ : J₂.ts = t₂) :
    THom Γ I ⟨I.mi, K.C, pre ++ t₂⟩ [.if_ bt c t el] := by
  obtain ⟨hmK, xs, hx, hCK, hcc, hcm⟩ := hc
  obtain ⟨-, xt, -, -, htc, htm⟩ := ht
  obtain ⟨-, xe, -, -, hec, hem⟩ := he
  rw [hJ₁] at htc htm
  rw [hJ₂] at hec hem
  refine ⟨rfl, xs ++ [], by simpa using hx, by simp [hCK], ?_, ?_⟩
  · have hi := InstrsOk.frame (InstrsOk.instr (InstrOk.if_ hbt htc hec)) hpre
    rw [← List.append_assoc, ← hts] at hi
    have hcc' : InstrsOk I.C (BExpr.lowerList c) ⟨I.ts, xs, K.ts⟩ := hcc
    rw [hCK] at hi
    simpa [BExpr.lower] using InstrsOk.seq hcc' hx hi
  · have hty' : K.C.types = I.mi.types := by rw [hCK, types_initLocals]; exact hty
    have e : K.ts.length - 1 - t₁.length + t₂.length = (pre ++ t₂).length := by
      rw [hts]; simp
    rw [forget_withLabel_of hCK] at htm hem
    show Mor Γ I.forget (some _) _
    rw [← e]
    exact mor_if (I := I.forget) hcm (blockArity_of_ok hty' hbt) (by rw [hts]; simp) htm
      (ftOut_endsAt ft₁ _) hem (ftOut_endsAt ft₂ _)

theorem thom_try {I J : TIface} {bt : BlockType} {cs : List Catch} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} {ns : List Nat} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hcok : ∀ c ∈ cs, CatchOk I.C c)
    (hcs : cs.mapM (clauseCount Γ.tags I.mi) = some ns)
    (hok : catchOk (I.C.labels.map List.length) cs ns = true)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.tryTable bt cs body] := by
  obtain ⟨-, xs, -, -, hbc, hbm⟩ := hb
  rw [hJ] at hbc hbm
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts]
    simpa [BExpr.lower] using
      InstrsOk.frame (InstrsOk.instr (InstrOk.tryTable hbt hbc hcok)) hpre
  · have e : I.ts.length - t₁.length + t₂.length = (pre ++ t₂).length := by
      rw [hts]; simp
    show Mor Γ I.forget (some _) _
    rw [← e]
    exact mor_try (I := I.forget) hcs (blockArity_of_ok hty hbt)
      (by simp [TIface.forget, hts]) hok hbm (ftOut_endsAt ft _)

/-! ## Operators -/

/-- An operator after its typed operands. -/
theorem tmor_op {I K : TIface} {i : Instr} {args : List BExpr} {pre t₁ t₂ : List CValType}
    {xs : List Nat} {ft : Bool} (ha : THom Γ I K args) (hts : K.ts = pre ++ t₁)
    (hpre : ResultOk K.C.toTypeCtx pre) (hi : InstrOk K.C i ⟨t₁, xs, t₂⟩)
    (hx : ∀ x ∈ xs, ∃ lt, K.C.locals[x]? = some lt)
    (hck : flatChkE (ehExt Γ.tags) Γ.funcs I.mi I.env.nl I.env.ret I.env.labels K.ts.length i =
      some (ftOut ft (pre ++ t₂).length)) :
    TMor Γ I ⟨I.mi, K.C.initLocals xs, pre ++ t₂⟩ ft [.op i args] := by
  obtain ⟨hmK, xa, hxa, hCK, hac, ham⟩ := ha
  refine ⟨rfl, xa ++ xs, inBounds_append hxa (hCK ▸ hx), by rw [hCK, Context.initLocals_append],
    ?_, ?_⟩
  · have hi' := InstrsOk.frame (InstrsOk.instr hi) hpre
    rw [← hts, hCK] at hi'
    have hac' : InstrsOk I.C (BExpr.lowerList args) ⟨I.ts, xa, K.ts⟩ := hac
    simpa using InstrsOk.seq hac' hxa hi'
  · exact mor_op (I := I.forget) ham hck

theorem lower_call (i : Instr) : BExpr.lowerList [.op i []] = [i] := by simp

theorem thom_call {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hts : I.ts = pre ++ ps.toList) (hpre : ResultOk I.C.toTypeCtx pre)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs))
    (hx : callArity Γ.funcs I.mi x = some (ps.toList.length, rs.toList.length)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.call x) []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    simpa using InstrsOk.frame (InstrsOk.instr (InstrOk.call hf he)) hpre
  · have e : I.ts.length - ps.toList.length + rs.toList.length = (pre ++ rs.toList).length := by
      rw [hts]; simp
    show Mor Γ I.forget (some _) _
    rw [← e]
    exact mor_call (I := I.forget) hx (by simp [TIface.forget, hts])

theorem thom_callIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType} {l : Limits}
    {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)} {pre : List CValType}
    (hts : I.ts = pre ++ (ps.toList ++ [a.valType])) (hpre : ResultOk I.C.toTypeCtx pre)
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hs : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callIndirect x y) []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    simpa using InstrsOk.frame (InstrsOk.instr (InstrOk.callIndirect ht hs hd he)) hpre
  · have e : I.ts.length - (ps.toList.length + 1) + rs.toList.length =
        (pre ++ rs.toList).length := by
      simp [hts]
    show Mor Γ I.forget (some _) _
    rw [← e]
    exact mor_callIndirect (I := I.forget) hy (by simp [TIface.forget, hts])

theorem thom_callRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hts : I.ts = pre ++ (ps.toList ++ [.refT true (.defHeap d)]))
    (hpre : ResultOk I.C.toTypeCtx pre) (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callRef y) []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    simpa using InstrsOk.frame (InstrsOk.instr (InstrOk.callRef hd he)) hpre
  · have e : I.ts.length - (ps.toList.length + 1) + rs.toList.length =
        (pre ++ rs.toList).length := by
      simp [hts]
    show Mor Γ I.forget (some _) _
    rw [← e]
    exact mor_callRef (I := I.forget) hy (by simp [TIface.forget, hts])

theorem ret_length {I : TIface} {rs' : List CValType} {rs : List CValType}
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs rs') :
    rs.length = I.env.ret := by
  simp only [TIface.env, hr, Option.getD_some]
  exact hs.length_eq

theorem tstop_returnCall {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hts : I.ts = t₃ ++ ps.toList)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄))
    (hx : callArity Γ.funcs I.mi x = some (ps.toList.length, rs.toList.length)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCall x) []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    exact InstrsOk.instr (InstrOk.returnCall hf he hr hs hok)
  · rw [ret_length hr hs] at hx
    exact mor_returnCall (I := I.forget) hx (by simp [TIface.forget, hts])

theorem tstop_returnCallIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType}
    {l : Limits} {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hts : I.ts = t₃ ++ ps.toList ++ [a.valType])
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hsub : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallIndirect x y) []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    exact InstrsOk.instr (InstrOk.returnCallIndirect ht hsub hd he hr hs hok)
  · rw [ret_length hr hs] at hy
    exact mor_returnCallIndirect (I := I.forget) hy (by simp [TIface.forget, hts])

theorem tstop_returnCallRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hts : I.ts = t₃ ++ ps.toList ++ [.refT true (.defHeap d)])
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallRef y) []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    exact InstrsOk.instr (InstrOk.returnCallRef hd he hr hs hok)
  · rw [ret_length hr hs] at hy
    exact mor_returnCallRef (I := I.forget) hy (by simp [TIface.forget, hts])

theorem tstop_throw {I : TIface} {x : TagIdx} {d : DefType} {ts : Ty (.list .val)}
    {t₁ t₂ : List CValType} (hts : I.ts = t₁ ++ ts.toList) (hx : I.C.tags[x.toNat]? = some d)
    (he : Expand d (.func ts .nil)) (hok : InstrTypeOk I.C (.plain t₁ t₂))
    (hf : tagFields Γ.tags I.mi x = some ts.toList.length) :
    TStop Γ I ⟨I.mi, I.C, t₂⟩ [.op (.throw x) []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    exact InstrsOk.instr (InstrOk.throw hx he hok)
  · exact mor_throw (I := I.forget) hf (by simp [TIface.forget, hts])

theorem tstop_throwRef {I : TIface} {t₁ t₂ : List CValType}
    (hts : I.ts = t₁ ++ [.refT true (.abs .exn)]) (hok : InstrTypeOk I.C (.plain t₁ t₂)) :
    TStop Γ I ⟨I.mi, I.C, t₂⟩ [.op .throwRef []] := by
  refine ⟨rfl, [], by simp, by simp, ?_, ?_⟩
  · rw [hts, lower_call]
    exact InstrsOk.instr (InstrOk.throwRef hok)
  · exact mor_throwRef (I := I.forget) (by simp [TIface.forget, hts])

/-! ## The forgetful functor -/

theorem tmor_forget {I J : TIface} {ft : Bool} {es : List BExpr} (h : TMor Γ I J ft es) :
    Mor Γ I.forget (ftOut ft J.forget.h) es := by
  obtain ⟨-, -, -, -, -, hc⟩ := h
  exact hc

theorem thom_forget {I J : TIface} {es : List BExpr} (h : THom Γ I J es) :
    Hom Γ I.forget J.forget es := by
  obtain ⟨hm, xs, -, hC, -, hc⟩ := h
  exact ⟨by simp only [TIface.forget, env_eq hm hC], hc⟩

theorem denTMor_sub {I J : TIface} {ft : Bool} :
    DenTMor (H := H) Γ I J ft ⊆ DenMor Γ I.forget (ftOut ft J.forget.h) := by
  rintro g ⟨es, h, rfl⟩
  exact ⟨es, tmor_forget h, rfl⟩

/-! ## Image closure -/

theorem idP_tmem {I : TIface} (hI : I.Ok) : (idP : PHom H Cfg ResP) ∈ DenTMor Γ I I true :=
  ⟨[], thom_id hI, denL_nil.symm⟩

theorem seqP_tmem {I J K : TIface} {ft : Bool} {g₁ g₂ : PHom H Cfg ResP}
    (h₁ : g₁ ∈ DenTMor Γ I J true) (h₂ : g₂ ∈ DenTMor Γ J K ft) :
    seqP g₁ g₂ ∈ DenTMor Γ I K ft := by
  obtain ⟨es₁, hm₁, rfl⟩ := h₁
  obtain ⟨es₂, hm₂, rfl⟩ := h₂
  exact ⟨es₁ ++ es₂, tmor_comp hm₁ hm₂, (denL_append es₁ es₂).symm⟩

theorem seqP_stop_tmem {I J K : TIface} {ft : Bool} {g₁ g₂ : PHom H Cfg ResP}
    (h₁ : g₁ ∈ DenTMor Γ I J false) (h₂ : g₂ ∈ DenTMor Γ J K ft) :
    seqP g₁ g₂ ∈ DenTMor Γ I K false := by
  obtain ⟨es₁, hm₁, rfl⟩ := h₁
  obtain ⟨es₂, hm₂, rfl⟩ := h₂
  exact ⟨es₁ ++ es₂, tmor_stop hm₁ hm₂, (denL_append es₁ es₂).symm⟩

theorem opP_tmem {I K : TIface} {i : Instr} {pre t₁ t₂ : List CValType} {xs : List Nat}
    {ft : Bool} {g : PHom H Cfg ResP} (hg : g ∈ DenTMor Γ I K true) (hts : K.ts = pre ++ t₁)
    (hpre : ResultOk K.C.toTypeCtx pre) (hi : InstrOk K.C i ⟨t₁, xs, t₂⟩)
    (hx : ∀ x ∈ xs, ∃ lt, K.C.locals[x]? = some lt)
    (hck : flatChkE (ehExt Γ.tags) Γ.funcs I.mi I.env.nl I.env.ret I.env.labels K.ts.length i =
      some (ftOut ft (pre ++ t₂).length)) :
    opP i g ∈ DenTMor Γ I ⟨I.mi, K.C.initLocals xs, pre ++ t₂⟩ ft := by
  obtain ⟨es, hm, rfl⟩ := hg
  exact ⟨[.op i es], tmor_op hm hts hpre hi hx hck, by rw [denL_singleton, denT_op]⟩

theorem blockP_tmem {I J : TIface} {bt : BlockType} {pre t₁ t₂ : List CValType} {ft : Bool}
    {g : PHom H Cfg ResP} (hty : I.C.types = I.mi.types) (hts : I.ts = pre ++ t₁)
    (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hg : g ∈ DenTMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft) (hJ : J.ts = t₂) :
    blockP bt g ∈ DenTMor Γ I ⟨I.mi, I.C, pre ++ t₂⟩ true := by
  obtain ⟨es, hm, rfl⟩ := hg
  exact ⟨[.block bt es], thom_block hty hts hpre hbt hm hJ, by rw [denL_singleton, denT_block]⟩

theorem loopP_tmem {I J : TIface} {bt : BlockType} {pre t₁ t₂ : List CValType} {ft : Bool}
    {g : PHom H Cfg ResP} (hty : I.C.types = I.mi.types) (hts : I.ts = pre ++ t₁)
    (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hg : g ∈ DenTMor Γ ⟨I.mi, I.C.withLabel t₁, t₁⟩ J ft) (hJ : J.ts = t₂) :
    loopP bt g ∈ DenTMor Γ I ⟨I.mi, I.C, pre ++ t₂⟩ true := by
  obtain ⟨es, hm, rfl⟩ := hg
  exact ⟨[.loop bt es], thom_loop hty hts hpre hbt hm hJ, by rw [denL_singleton, denT_loop]; rfl⟩

theorem ifP_tmem {I K J₁ J₂ : TIface} {bt : BlockType} {pre t₁ t₂ : List CValType}
    {ft₁ ft₂ : Bool} {gc gt ge : PHom H Cfg ResP} (hc : gc ∈ DenTMor Γ I K true)
    (hty : I.C.types = I.mi.types) (hts : K.ts = pre ++ t₁ ++ [.i32])
    (hpre : ResultOk K.C.toTypeCtx pre) (hbt : BlockTypeOk K.C bt t₁ t₂)
    (ht : gt ∈ DenTMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₁ ft₁) (hJ₁ : J₁.ts = t₂)
    (he : ge ∈ DenTMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₂ ft₂) (hJ₂ : J₂.ts = t₂) :
    ifP bt gc gt ge ∈ DenTMor Γ I ⟨I.mi, K.C, pre ++ t₂⟩ true := by
  obtain ⟨c, hcm, rfl⟩ := hc
  obtain ⟨t, htm, rfl⟩ := ht
  obtain ⟨el, hem, rfl⟩ := he
  exact ⟨[.if_ bt c t el], thom_if hcm hty hts hpre hbt htm hJ₁ hem hJ₂,
    by rw [denL_singleton, denT_if]⟩

theorem tryP_tmem {I J : TIface} {bt : BlockType} {cs : List Catch} {pre t₁ t₂ : List CValType}
    {ft : Bool} {ns : List Nat} {g : PHom H Cfg ResP} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hcok : ∀ c ∈ cs, CatchOk I.C c) (hcs : cs.mapM (clauseCount Γ.tags I.mi) = some ns)
    (hok : catchOk (I.C.labels.map List.length) cs ns = true)
    (hg : g ∈ DenTMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft) (hJ : J.ts = t₂) :
    tryP bt cs g ∈ DenTMor Γ I ⟨I.mi, I.C, pre ++ t₂⟩ true := by
  obtain ⟨es, hm, rfl⟩ := hg
  exact ⟨[.tryTable bt cs es], thom_try hty hts hpre hbt hcok hcs hok hm hJ,
    by rw [denL_singleton, denT_try]⟩

end Silmaril.Proofs.Wasm.Abstract.ExposePTyped
