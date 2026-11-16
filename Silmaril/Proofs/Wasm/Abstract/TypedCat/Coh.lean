module

public import Silmaril.Wasm.Abstract.TypedCat.Defs
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCat.Thms`: coherence (`Coh`) gives every run-time arity
the checker reads (`callArity`, `typeArity`, `tagFields`, `clauseCount` with `catchOk`) from
Core typing, it is kept along typed code, and every state a typed interface describes makes it
coherent. So the closure of the typed subcategory holds with typing and coherence only.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.CallXT (typeArity)

variable {H : Type} {Γ : Ctx H}

/-! ## Arities from coherence -/

theorem funcType_of_expand' {d : DefType} {ps rs : Ty (.list .val)} (h : Expand d (.func ps rs)) :
    DefType.funcType? d = some (ps.toList, rs.toList) := by
  simp [DefType.funcType?, Expand.iff.1 h]

theorem callArity_of_coh {I : TIface} (hco : Coh Γ I) {x : FuncIdx} {d : DefType}
    {ps rs : Ty (.list .val)} (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs)) :
    callArity Γ.funcs I.mi x = some (ps.toList.length, rs.toList.length) := by
  obtain ⟨a, fi, ha, hfi, hok, hd⟩ := hco.funcs _ _ hf
  obtain ⟨ps', rs', he', h₁, h₂⟩ := PC.func_sub_data hd hok he
  simp [callArity, ha, hfi, funcType_of_expand' he', h₁.length_eq, h₂.length_eq]

theorem typeArity_of_coh {I : TIface} (hco : Coh Γ I) {y : TypeIdx} {d : DefType}
    {ps rs : Ty (.list .val)} (hd : I.C.type? y = some d) (he : Expand d (.func ps rs)) :
    typeArity I.mi y = some (ps.toList.length, rs.toList.length) := by
  have hd' : I.mi.types[y.toNat]? = some d := by
    rw [← hco.types]; exact hd
  simp [Silmaril.Wasm.Abstract.CallXT.typeArity, hd', funcType_of_expand' he]

theorem tagFields_of_coh {I : TIface} (hco : Coh Γ I) {x : TagIdx} {d : DefType}
    {ts : Ty (.list .val)} (hx : I.C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil)) :
    tagFields Γ.tags I.mi x = some ts.toList.length := by
  obtain ⟨a, ti, ha, hti, rfl⟩ := hco.tags _ _ hx
  have hty : DefType.funcType? ti.type =
      some (ts.toList, (Ty.nil : Ty (.list .val)).toList) := funcType_of_expand' he
  simp only [tagFields, ha, hti, Option.bind_eq_bind, Option.bind_some, hty]
  rfl

theorem labels_map {C : Context} {l : LabelIdx} {lt : List CValType}
    (hl : C.labels[l.toNat]? = some lt) :
    (C.labels.map List.length)[l.toNat]? = some lt.length := by
  simp [hl]

/-- One clause: the values it pushes, and its label's arity is at most that. -/
theorem clause_of_coh {I : TIface} (hco : Coh Γ I) {c : Catch} (hc : CatchOk I.C c) :
    ∃ n, clauseCount Γ.tags I.mi c = some n ∧
      ∃ m, (I.C.labels.map List.length)[(catchLabel c).toNat]? = some m ∧ m ≤ n := by
  cases hc with
  | catch_ hx he hl hs =>
    exact ⟨_, tagFields_of_coh hco hx he, _, labels_map hl, hs.length_eq.symm.le⟩
  | @catchRef x l d ts lt hx he hl hs =>
    refine ⟨ts.toList.length + 1, by simp [clauseCount, tagFields_of_coh hco hx he], _,
      labels_map hl, ?_⟩
    have := hs.length_eq; simp at this; omega
  | catchAll hl hs =>
    refine ⟨0, rfl, _, labels_map hl, ?_⟩
    have := hs.length_eq; simp at this; omega
  | catchAllRef hl hs =>
    refine ⟨1, rfl, _, labels_map hl, ?_⟩
    have := hs.length_eq; simp at this; omega

theorem catchOk_cons {L : List Nat} {c : Catch} {cs : List Catch} {n : Nat} {ns : List Nat}
    {m : Nat} (hm : L[(catchLabel c).toNat]? = some m) (hle : m ≤ n)
    (h : catchOk L cs ns = true) : catchOk L (c :: cs) (n :: ns) = true := by
  simp only [catchOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h ⊢
  refine ⟨by simp [h.1], ?_⟩
  intro p hp
  simp only [List.zip_cons_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · simp [hm, hle]
  · exact h.2 p hp

/-- **The clauses of a typed `try_table`** push values the checker reads, accepted at their
labels. -/
theorem clauses_of_coh {I : TIface} (hco : Coh Γ I) :
    ∀ {cs : List Catch}, (∀ c ∈ cs, CatchOk I.C c) →
      ∃ ns, cs.mapM (clauseCount Γ.tags I.mi) = some ns ∧
        catchOk (I.C.labels.map List.length) cs ns = true
  | [], _ => ⟨[], rfl, rfl⟩
  | c :: cs, h => by
    obtain ⟨n, hn, m, hm, hle⟩ := clause_of_coh hco (h c (by simp))
    obtain ⟨ns, hns, hok⟩ := clauses_of_coh hco (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    exact ⟨n :: ns, by simp [List.mapM_cons, hn, hns], catchOk_cons hm hle hok⟩

/-! ## Coherence is kept along typed code -/

theorem initLocals_funcs (C : Context) (xs : List Nat) : (C.initLocals xs).funcs = C.funcs := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs
  rw [hL]

theorem initLocals_tags (C : Context) (xs : List Nat) : (C.initLocals xs).tags = C.tags := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs
  rw [hL]

theorem initLocals_types (C : Context) (xs : List Nat) : (C.initLocals xs).types = C.types :=
  congrArg TypeCtx.types (Context.initLocals_toTypeCtx C xs)

theorem coh_initLocals {I : TIface} (hco : Coh Γ I) (xs : List Nat) (ts : List CValType) :
    Coh Γ ⟨I.mi, I.C.initLocals xs, ts⟩ :=
  ⟨(initLocals_types I.C xs).trans hco.types,
    fun x d hx => hco.funcs x d (by rw [← initLocals_funcs I.C xs]; exact hx),
    fun x d hx => hco.tags x d (by rw [← initLocals_tags I.C xs]; exact hx)⟩

theorem coh_withLabel {I : TIface} (hco : Coh Γ I) (L ts : List CValType) :
    Coh Γ ⟨I.mi, I.C.withLabel L, ts⟩ :=
  ⟨hco.types, hco.funcs, hco.tags⟩

theorem coh_stack {I : TIface} (hco : Coh Γ I) (ts : List CValType) : Coh Γ ⟨I.mi, I.C, ts⟩ :=
  ⟨hco.types, hco.funcs, hco.tags⟩

theorem coh_of_tmor {I J : TIface} {ft : Bool} {es : List BExpr} (h : TMor Γ I J ft es)
    (hco : Coh Γ I) : Coh Γ J := by
  obtain ⟨hm, xs, -, hC, -⟩ := h
  refine ⟨?_, fun x d hx => ?_, fun x d hx => ?_⟩
  · rw [hC, hm, initLocals_types]; exact hco.types
  · rw [hm]; rw [hC, initLocals_funcs] at hx; exact hco.funcs x d hx
  · rw [hm]; rw [hC, initLocals_tags] at hx; exact hco.tags x d hx

/-! ## Typed states are coherent -/

/-- A function address typed at `d` is a store function. -/
theorem externAddr_func_some {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : ∀ {a : Nat}, xa = .func a → ∃ fi, s.funcs[a]? = some fi := by
  induction h with
  | func h => intro a ha; cases ha; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih
  | _ => intro a ha; cases ha

theorem realizes_coh {I : TIface} {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) : Coh Γ I := by
  obtain ⟨hg, hS, hfm, ⟨C₀, hF, hIC⟩, -⟩ := hr
  obtain ⟨C₁, lts, hm, -, rfl⟩ := hF
  have hfun : I.C.funcs = C₁.funcs := by rw [hIC]
  have htag : I.C.tags = C₁.tags := by rw [hIC]
  have hty : I.C.types = C₁.types := by rw [hIC]
  cases hm with
  | mk _ htags _ hfuncs =>
    refine ⟨?_, fun x d hx => ?_, fun x d hx => ?_⟩
    · rw [hty, ← hfm]
    · rw [hfun] at hx
      obtain ⟨a, ha, hxa⟩ := forall₂_getElem?_right hfuncs hx
      obtain ⟨fi, hfi⟩ := externAddr_func_some hxa rfl
      refine ⟨a, fi, hfm ▸ ha, hg.1 ▸ hfi, PC.StoreOk.func_tyOk hS hfi, ?_⟩
      exact PC.externAddr_func hxa rfl hfi rfl
    · rw [htag] at hx
      obtain ⟨a, ha, hxa⟩ := forall₂_getElem?_right htags hx
      obtain ⟨ti, hti, hte⟩ := ExternAddrOk.tag_inv hS hxa
      cases hte
      exact ⟨a, ti, hfm ▸ ha, hg.2.1 ▸ hti, rfl⟩

/-! ## The closure with the premises discharged -/

theorem thom_block {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hco : Coh Γ I)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.block bt body] :=
  Silmaril.Wasm.Abstract.ExposePTyped.thom_block hco.types hts hpre hbt hb hJ

theorem thom_loop {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hco : Coh Γ I)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₁, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.loop bt body] :=
  Silmaril.Wasm.Abstract.ExposePTyped.thom_loop hco.types hts hpre hbt hb hJ

theorem thom_if {I K J₁ J₂ : TIface} {bt : BlockType} {c t el : List BExpr}
    {pre t₁ t₂ : List CValType} {ft₁ ft₂ : Bool} (hco : Coh Γ I) (hc : THom Γ I K c)
    (hts : K.ts = pre ++ t₁ ++ [.i32])
    (hpre : ResultOk K.C.toTypeCtx pre) (hbt : BlockTypeOk K.C bt t₁ t₂)
    (ht : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₁ ft₁ t) (hJ₁ : J₁.ts = t₂)
    (he : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₂ ft₂ el) (hJ₂ : J₂.ts = t₂) :
    THom Γ I ⟨I.mi, K.C, pre ++ t₂⟩ [.if_ bt c t el] :=
  Silmaril.Wasm.Abstract.ExposePTyped.thom_if hc hco.types hts hpre hbt ht hJ₁ he hJ₂

theorem thom_try {I J : TIface} {bt : BlockType} {cs : List Catch} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hco : Coh Γ I)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hcok : ∀ c ∈ cs, CatchOk I.C c)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.tryTable bt cs body] := by
  obtain ⟨ns, hcs, hok⟩ := clauses_of_coh hco hcok
  exact Silmaril.Wasm.Abstract.ExposePTyped.thom_try hco.types hts hpre hbt hcok hcs hok hb hJ

theorem thom_call {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hco : Coh Γ I) (hts : I.ts = pre ++ ps.toList)
    (hpre : ResultOk I.C.toTypeCtx pre)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.call x) []] :=
  Silmaril.Wasm.Abstract.ExposePTyped.thom_call hts hpre hf he (callArity_of_coh hco hf he)

theorem thom_callIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType} {l : Limits}
    {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)} {pre : List CValType}
    (hco : Coh Γ I)
    (hts : I.ts = pre ++ (ps.toList ++ [a.valType])) (hpre : ResultOk I.C.toTypeCtx pre)
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hs : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callIndirect x y) []] :=
  Silmaril.Wasm.Abstract.ExposePTyped.thom_callIndirect hts hpre ht hs hd he
    (typeArity_of_coh hco hd he)

theorem thom_callRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hco : Coh Γ I)
    (hts : I.ts = pre ++ (ps.toList ++ [.refT true (.defHeap d)]))
    (hpre : ResultOk I.C.toTypeCtx pre) (hd : I.C.type? y = some d) (he : Expand d (.func ps rs)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callRef y) []] :=
  Silmaril.Wasm.Abstract.ExposePTyped.thom_callRef hts hpre hd he (typeArity_of_coh hco hd he)

theorem tstop_returnCall {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hco : Coh Γ I) (hts : I.ts = t₃ ++ ps.toList)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCall x) []] :=
  Silmaril.Wasm.Abstract.ExposePTyped.tstop_returnCall hts hf he hr hs hok
    (callArity_of_coh hco hf he)

theorem tstop_returnCallIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType}
    {l : Limits} {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hco : Coh Γ I) (hts : I.ts = t₃ ++ ps.toList ++ [a.valType])
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hsub : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallIndirect x y) []] :=
  Silmaril.Wasm.Abstract.ExposePTyped.tstop_returnCallIndirect hts ht hsub hd he hr hs hok
    (typeArity_of_coh hco hd he)

theorem tstop_returnCallRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hco : Coh Γ I)
    (hts : I.ts = t₃ ++ ps.toList ++ [.refT true (.defHeap d)])
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallRef y) []] :=
  Silmaril.Wasm.Abstract.ExposePTyped.tstop_returnCallRef hts hd he hr hs hok
    (typeArity_of_coh hco hd he)

theorem tstop_throw {I : TIface} {x : TagIdx} {d : DefType} {ts : Ty (.list .val)}
    {t₁ t₂ : List CValType} (hco : Coh Γ I) (hts : I.ts = t₁ ++ ts.toList)
    (hx : I.C.tags[x.toNat]? = some d)
    (he : Expand d (.func ts .nil)) (hok : InstrTypeOk I.C (.plain t₁ t₂)) :
    TStop Γ I ⟨I.mi, I.C, t₂⟩ [.op (.throw x) []] :=
  Silmaril.Wasm.Abstract.ExposePTyped.tstop_throw hts hx he hok (tagFields_of_coh hco hx he)

end Silmaril.Proofs.Wasm.Abstract.TypedCat
