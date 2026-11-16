module

public import Silmaril.Wasm.Abstract.ExposePTyped.Defs
public import Silmaril.Wasm.Abstract.ExposePStruct.Thms
import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Cat
import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Realize
import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Tensor

/-!
# The Core-typed subcategory of the exact F5 denotation, and the answered stack tensor: theorems

**The typed subcategory** (`TIface`, `TMor`, `THom`, `TStop`; see Defs). Objects are Core
validation contexts with a module instance and a stack of value types; morphisms are code whose
lowering is Core-typed between them and which passes #529's arity check.

* **Closure.** The identity (`thom_id`, at an object whose stack types are valid), composition
  (`tmor_comp`; after code that never falls through, anything typed: `tmor_stop`), operators
  after their operands (`tmor_op`, any Core-typed instruction the check accepts), `block`,
  `loop`, `if`, `try_table` (`thom_block`, `thom_loop`, `thom_if`, `thom_try`: the Core block type
  and body typing, the instance's types being the context's, `I.C.types = I.mi.types`, which
  gives the check's block arity), the call forms (`thom_call`, `thom_callIndirect`,
  `thom_callRef`), the tail calls, ending the morphism at a never-falls-through target at any
  Core stack (`tstop_returnCall`, `tstop_returnCallIndirect`, `tstop_returnCallRef`), and
  `throw`/`throw_ref` (`tstop_throw`, `tstop_throwRef`). The premises are Core's typing rule and
  the arity the check reads from the run-time context `Γ` (the callee's `callArity` in the store's
  functions, the annotated `typeArity`, the tag's `tagFields`, the clauses' `clauseCount` and
  `catchOk`), which Core typing does not determine without a store typing.
* **The forgetful functor** to #529's checked category is the identity on code
  (`tmor_forget`, `thom_forget`: typed ⇒ checked, sending `THom` to `Hom`), so it preserves
  identities (`[]`) and composition (`++`), and the typed image is in the checked image
  (`denTMor_sub`): image closure transfers.
* **Typed code is a typed problem** (`tmor_typedP`): at every run state its interface describes
  (`Realizes`), with valid stack types at both ends, a typed morphism is `Interp.TypedP` code:
  the check, and its Core configuration typed in context.
* **Image closure.** `DenTMor` is closed under the operations on bodies: `idP_tmem`, `seqP_tmem`,
  `seqP_stop_tmem`, `opP_tmem`, `blockP_tmem`, `loopP_tmem`, `ifP_tmem`, `tryP_tmem`.

**The answered stack tensor** (`ArityResp`, `whiskO`, `trimO`, `GoodO`; see Defs). #529's
`denListXP_whisker` is an equation of `BodyM` computations for stack-pure code; for the call
forms, `throw` and `try_table` no such equation holds pointwise in the monad (#529's
`ExposePStruct.Thms` gives the counterexample `[call x, drop]` with an answer short of the
callee's results). With an oracle `C` that respects arities (from a store agreeing with `Γ` its
answers agree with `Γ`: functions, tags, well-formed exceptions; and return at least the
callee's declared result count) the tensor holds for the answered semantics `CallXP.EvalOXP C`
relationally, on **all** checked code:

* `evalOXP_goodO`, `mor_goodO`: a checked run keeps `Γ`, its frame's instance and local count, and
  ends as its check says (a fallthrough at the checked height, branches and returns with at least
  their target's arity);
* `evalOXP_tensor`, `mor_tensor`, `tmor_tensor`: the runs on `stk ++ rest` (to a store `s'`, a
  frame `f'`, read through `trimO`) are exactly the runs on `stk` to the same `s'` and `f'`, their
  result whiskered by `whiskO rest` and read through `trimO`. The hypotheses used, exactly: the
  arity-respecting oracle (a call's continuation stack is at the checked height only when the
  answer has the callee's result count), the store's tag instances being `Γ`'s with exceptions of
  their tag's field count (`TagsOk`, so `throw` pops the checked field count and a caught
  exception pushes at least its label's arity), and the store's functions being `Γ`'s (so a
  call pops the checked parameter count). `throw`, `try_table` and the tail calls need no
  hypothesis on the answers.
-/

public section

namespace Silmaril.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.CallXT (typeArity)
open Silmaril.Wasm.Abstract.ExposeP (ResP)
open Silmaril.Wasm.Abstract.CallXP (EvalOXP POut)

variable {H : Type} {Γ : Ctx H} {C : Abstract.CallRel H}

/-! ## The typed subcategory: closure -/

theorem thom_id {I : TIface} (hI : I.Ok) : THom Γ I I [] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_id hI

theorem tmor_comp {I J K : TIface} {ft : Bool} {es₁ es₂ : List BExpr} (h₁ : THom Γ I J es₁)
    (h₂ : TMor Γ J K ft es₂) : TMor Γ I K ft (es₁ ++ es₂) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tmor_comp h₁ h₂

theorem tmor_stop {I J K : TIface} {ft : Bool} {es₁ es₂ : List BExpr} (h₁ : TStop Γ I J es₁)
    (h₂ : TMor Γ J K ft es₂) : TStop Γ I K (es₁ ++ es₂) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tmor_stop h₁ h₂

theorem thom_block {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.block bt body] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_block hty hts hpre hbt hb hJ

theorem thom_loop {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₁, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.loop bt body] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_loop hty hts hpre hbt hb hJ

theorem thom_if {I K J₁ J₂ : TIface} {bt : BlockType} {c t el : List BExpr}
    {pre t₁ t₂ : List CValType} {ft₁ ft₂ : Bool} (hc : THom Γ I K c)
    (hty : I.C.types = I.mi.types) (hts : K.ts = pre ++ t₁ ++ [.i32])
    (hpre : ResultOk K.C.toTypeCtx pre) (hbt : BlockTypeOk K.C bt t₁ t₂)
    (ht : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₁ ft₁ t) (hJ₁ : J₁.ts = t₂)
    (he : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₂ ft₂ el) (hJ₂ : J₂.ts = t₂) :
    THom Γ I ⟨I.mi, K.C, pre ++ t₂⟩ [.if_ bt c t el] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_if hc hty hts hpre hbt ht hJ₁ he hJ₂

theorem thom_try {I J : TIface} {bt : BlockType} {cs : List Catch} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} {ns : List Nat} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hcok : ∀ c ∈ cs, CatchOk I.C c)
    (hcs : cs.mapM (clauseCount Γ.tags I.mi) = some ns)
    (hok : catchOk (I.C.labels.map List.length) cs ns = true)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.tryTable bt cs body] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_try hty hts hpre hbt hcok hcs hok hb hJ

/-- An operator after its typed operands. -/
theorem tmor_op {I K : TIface} {i : Instr} {args : List BExpr} {pre t₁ t₂ : List CValType}
    {xs : List Nat} {ft : Bool} (ha : THom Γ I K args) (hts : K.ts = pre ++ t₁)
    (hpre : ResultOk K.C.toTypeCtx pre) (hi : InstrOk K.C i ⟨t₁, xs, t₂⟩)
    (hx : ∀ x ∈ xs, ∃ lt, K.C.locals[x]? = some lt)
    (hck : flatChkE (ehExt Γ.tags) Γ.funcs I.mi I.env.nl I.env.ret I.env.labels K.ts.length i =
      some (ftOut ft (pre ++ t₂).length)) :
    TMor Γ I ⟨I.mi, K.C.initLocals xs, pre ++ t₂⟩ ft [.op i args] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tmor_op ha hts hpre hi hx hck

theorem thom_call {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hts : I.ts = pre ++ ps.toList) (hpre : ResultOk I.C.toTypeCtx pre)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs))
    (hx : callArity Γ.funcs I.mi x = some (ps.toList.length, rs.toList.length)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.call x) []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_call hts hpre hf he hx

theorem thom_callIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType} {l : Limits}
    {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)} {pre : List CValType}
    (hts : I.ts = pre ++ (ps.toList ++ [a.valType])) (hpre : ResultOk I.C.toTypeCtx pre)
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hs : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callIndirect x y) []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_callIndirect hts hpre ht hs hd he hy

theorem thom_callRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hts : I.ts = pre ++ (ps.toList ++ [.refT true (.defHeap d)]))
    (hpre : ResultOk I.C.toTypeCtx pre) (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callRef y) []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_callRef hts hpre hd he hy

theorem tstop_returnCall {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hts : I.ts = t₃ ++ ps.toList)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄))
    (hx : callArity Γ.funcs I.mi x = some (ps.toList.length, rs.toList.length)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCall x) []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tstop_returnCall hts hf he hr hs hok hx

theorem tstop_returnCallIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType}
    {l : Limits} {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hts : I.ts = t₃ ++ ps.toList ++ [a.valType])
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hsub : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallIndirect x y) []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tstop_returnCallIndirect hts ht hsub hd he hr hs hok hy

theorem tstop_returnCallRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hts : I.ts = t₃ ++ ps.toList ++ [.refT true (.defHeap d)])
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄))
    (hy : typeArity I.mi y = some (ps.toList.length, rs.toList.length)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallRef y) []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tstop_returnCallRef hts hd he hr hs hok hy

theorem tstop_throw {I : TIface} {x : TagIdx} {d : DefType} {ts : Ty (.list .val)}
    {t₁ t₂ : List CValType} (hts : I.ts = t₁ ++ ts.toList) (hx : I.C.tags[x.toNat]? = some d)
    (he : Expand d (.func ts .nil)) (hok : InstrTypeOk I.C (.plain t₁ t₂))
    (hf : tagFields Γ.tags I.mi x = some ts.toList.length) :
    TStop Γ I ⟨I.mi, I.C, t₂⟩ [.op (.throw x) []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tstop_throw hts hx he hok hf

theorem tstop_throwRef {I : TIface} {t₁ t₂ : List CValType}
    (hts : I.ts = t₁ ++ [.refT true (.abs .exn)]) (hok : InstrTypeOk I.C (.plain t₁ t₂)) :
    TStop Γ I ⟨I.mi, I.C, t₂⟩ [.op .throwRef []] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tstop_throwRef hts hok

/-! ## The forgetful functor to the checked category -/

theorem tmor_forget {I J : TIface} {ft : Bool} {es : List BExpr} (h : TMor Γ I J ft es) :
    Mor Γ I.forget (ftOut ft J.forget.h) es :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tmor_forget h

theorem thom_forget {I J : TIface} {es : List BExpr} (h : THom Γ I J es) :
    Hom Γ I.forget J.forget es :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.thom_forget h

theorem denTMor_sub {I J : TIface} {ft : Bool} :
    DenTMor (H := H) Γ I J ft ⊆ DenMor Γ I.forget (ftOut ft J.forget.h) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.denTMor_sub

/-! ## Image closure -/

theorem idP_tmem {I : TIface} (hI : I.Ok) : (idP : PHom H Cfg ResP) ∈ DenTMor Γ I I true :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.idP_tmem hI

theorem seqP_tmem {I J K : TIface} {ft : Bool} {g₁ g₂ : PHom H Cfg ResP}
    (h₁ : g₁ ∈ DenTMor Γ I J true) (h₂ : g₂ ∈ DenTMor Γ J K ft) :
    seqP g₁ g₂ ∈ DenTMor Γ I K ft :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.seqP_tmem h₁ h₂

theorem seqP_stop_tmem {I J K : TIface} {ft : Bool} {g₁ g₂ : PHom H Cfg ResP}
    (h₁ : g₁ ∈ DenTMor Γ I J false) (h₂ : g₂ ∈ DenTMor Γ J K ft) :
    seqP g₁ g₂ ∈ DenTMor Γ I K false :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.seqP_stop_tmem h₁ h₂

theorem opP_tmem {I K : TIface} {i : Instr} {pre t₁ t₂ : List CValType} {xs : List Nat}
    {ft : Bool} {g : PHom H Cfg ResP} (hg : g ∈ DenTMor Γ I K true) (hts : K.ts = pre ++ t₁)
    (hpre : ResultOk K.C.toTypeCtx pre) (hi : InstrOk K.C i ⟨t₁, xs, t₂⟩)
    (hx : ∀ x ∈ xs, ∃ lt, K.C.locals[x]? = some lt)
    (hck : flatChkE (ehExt Γ.tags) Γ.funcs I.mi I.env.nl I.env.ret I.env.labels K.ts.length i =
      some (ftOut ft (pre ++ t₂).length)) :
    opP i g ∈ DenTMor Γ I ⟨I.mi, K.C.initLocals xs, pre ++ t₂⟩ ft :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.opP_tmem hg hts hpre hi hx hck

theorem blockP_tmem {I J : TIface} {bt : BlockType} {pre t₁ t₂ : List CValType} {ft : Bool}
    {g : PHom H Cfg ResP} (hty : I.C.types = I.mi.types) (hts : I.ts = pre ++ t₁)
    (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hg : g ∈ DenTMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft) (hJ : J.ts = t₂) :
    blockP bt g ∈ DenTMor Γ I ⟨I.mi, I.C, pre ++ t₂⟩ true :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.blockP_tmem hty hts hpre hbt hg hJ

theorem loopP_tmem {I J : TIface} {bt : BlockType} {pre t₁ t₂ : List CValType} {ft : Bool}
    {g : PHom H Cfg ResP} (hty : I.C.types = I.mi.types) (hts : I.ts = pre ++ t₁)
    (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hg : g ∈ DenTMor Γ ⟨I.mi, I.C.withLabel t₁, t₁⟩ J ft) (hJ : J.ts = t₂) :
    loopP bt g ∈ DenTMor Γ I ⟨I.mi, I.C, pre ++ t₂⟩ true :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.loopP_tmem hty hts hpre hbt hg hJ

theorem ifP_tmem {I K J₁ J₂ : TIface} {bt : BlockType} {pre t₁ t₂ : List CValType}
    {ft₁ ft₂ : Bool} {gc gt ge : PHom H Cfg ResP} (hc : gc ∈ DenTMor Γ I K true)
    (hty : I.C.types = I.mi.types) (hts : K.ts = pre ++ t₁ ++ [.i32])
    (hpre : ResultOk K.C.toTypeCtx pre) (hbt : BlockTypeOk K.C bt t₁ t₂)
    (ht : gt ∈ DenTMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₁ ft₁) (hJ₁ : J₁.ts = t₂)
    (he : ge ∈ DenTMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₂ ft₂) (hJ₂ : J₂.ts = t₂) :
    ifP bt gc gt ge ∈ DenTMor Γ I ⟨I.mi, K.C, pre ++ t₂⟩ true :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.ifP_tmem hc hty hts hpre hbt ht hJ₁ he hJ₂

theorem tryP_tmem {I J : TIface} {bt : BlockType} {cs : List Catch} {pre t₁ t₂ : List CValType}
    {ft : Bool} {ns : List Nat} {g : PHom H Cfg ResP} (hty : I.C.types = I.mi.types)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hcok : ∀ c ∈ cs, CatchOk I.C c) (hcs : cs.mapM (clauseCount Γ.tags I.mi) = some ns)
    (hok : catchOk (I.C.labels.map List.length) cs ns = true)
    (hg : g ∈ DenTMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft) (hJ : J.ts = t₂) :
    tryP bt cs g ∈ DenTMor Γ I ⟨I.mi, I.C, pre ++ t₂⟩ true :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tryP_tmem hty hts hpre hbt hcok hcs hok hg hJ

/-! ## Typed code is a typed problem -/

/-- **Typed code is a typed problem** at every run state its interface describes. -/
theorem tmor_typedP {I J : TIface} {ft : Bool} {es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (h : TMor Γ I J ft es) (hr : Realizes Γ I s f stk) (hI : I.Ok)
    (hJ : J.Ok) : TypedP Γ.tags s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tmor_typedP h hr hI hJ

/-! ## The answered stack tensor -/

/-- **The result invariant of an answered run** of checked code under an arity-respecting
oracle: the store keeps agreeing with `Γ`, the frame keeps its instance and local count, and
the result ends as the check says (`GoodO`). -/
theorem evalOXP_goodO (hC : ArityResp Γ C) {s s' : Store H} {f f' : Frame} {stk : List Val}
    {es : List BExpr} {o : POut} {labels : List Nat} {ret : Nat} {oc : Option Nat}
    (d : EvalOXP C s f stk es (s', f', o)) (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc) :
    Γ.Good s' ∧ f'.module = f.module ∧ f'.locals.length = f.locals.length ∧
      GoodO labels ret oc o :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.evalOXP_goodO hC d hg hc

/-- **The answered stack tensor.** Under an arity-respecting oracle, for checked code (every
form: calls, tail calls, `throw`, `throw_ref`, `try_table` included), the runs on `stk ++ rest`
read at their target's arity are exactly the runs on `stk` with `rest` appended below the
fallthrough (`whiskO`), read at their target's arity (`trimO`): the same stores and frames, in
both directions. -/
theorem evalOXP_tensor (hC : ArityResp Γ C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {labels : List Nat} {ret : Nat} {oc : Option Nat} (hg : Γ.Good s)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some oc)
    (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO labels ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧ trimO labels ret (whiskO rest o) = X :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.evalOXP_tensor hC hg hc rest s' f' X

/-- The result invariant for #529's checked morphisms. -/
theorem mor_goodO (hC : ArityResp Γ C) {I : Iface} {oc : Option Nat} {es : List BExpr}
    (hm : Mor Γ I oc es) {s s' : Store H} {f f' : Frame} {stk : List Val} {o : POut}
    (d : EvalOXP C s f stk es (s', f', o)) (hg : Γ.Good s)
    (hf : f.module = I.env.mi) (hn : f.locals.length = I.env.nl) (hs : stk.length = I.h) :
    Γ.Good s' ∧ f'.module = f.module ∧ f'.locals.length = f.locals.length ∧
      GoodO I.env.labels I.env.ret oc o :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.mor_goodO hC hm d hg hf hn hs

/-- **The answered stack tensor for #529's checked morphisms** (`mor_whisker` beyond stack-pure
code). -/
theorem mor_tensor (hC : ArityResp Γ C) {I : Iface} {oc : Option Nat} {es : List BExpr}
    (hm : Mor Γ I oc es) {s : Store H} {f : Frame} {stk : List Val} (hg : Γ.Good s)
    (hf : f.module = I.env.mi) (hn : f.locals.length = I.env.nl) (hs : stk.length = I.h)
    (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.mor_tensor hC hm hg hf hn hs rest s' f' X

/-- **The answered stack tensor for typed morphisms**, at every run state the interface
describes. -/
theorem tmor_tensor (hC : ArityResp Γ C) {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X :=
  Silmaril.Proofs.Wasm.Abstract.ExposePTyped.tmor_tensor hC hm hr rest s' f' X

end Silmaril.Wasm.Abstract.ExposePTyped
