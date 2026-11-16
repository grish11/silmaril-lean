module

public import Silmaril.Wasm.Abstract.TypedCat.Defs
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
public import Silmaril.Wasm.Abstract.XRecursionP.Defs
import Silmaril.Proofs.Wasm.Abstract.TypedCat.Coh
import Silmaril.Proofs.Wasm.Abstract.TypedCat.Shift
import Silmaril.Proofs.Wasm.Abstract.TypedCat.Strength
import Silmaril.Proofs.Wasm.Abstract.TypedCat.Answer
import Silmaril.Proofs.Wasm.Abstract.TypedCat.Interchange

/-!
# The typed subcategory with its premises discharged, the frame rule and strength: theorems

**A. Closure from typing and coherence.** #540's closure lemmas take the checker's run-time
arities as premises. Coherence (`Coh Γ I`, see Defs) gives each of them from Core typing:

* `callArity_of_coh`: a context function of type `d` expanding to `ps → rs` has the checker's
  `callArity` `(|ps|, |rs|)`: its store function's type is `d` or a valid subtype of it, and
  subtyping of defined function types keeps the counts (`PC.func_sub_data`);
* `typeArity_of_coh`: an annotated type `y` has the checker's `typeArity`, since the context's
  types are the instance's;
* `tagFields_of_coh`: a context tag of type `ts → []` has `tagFields` `|ts|`;
* `clauses_of_coh`: the clauses of a `try_table`, each `Catch_ok`, push `clauseCount` values,
  accepted by `catchOk` at their labels (a label's type is a supertype of the pushed types, so of
  the same length).

So `thom_block`, `thom_loop`, `thom_if`, `thom_try`, `thom_call`, `thom_callIndirect`,
`thom_callRef`, `tstop_returnCall`, `tstop_returnCallIndirect`, `tstop_returnCallRef` and
`tstop_throw` hold with Core's typing rule and `Coh Γ I` as their only further hypothesis
(composition `ExposePTyped.tmor_comp` and `tstop_throwRef` never needed one). Coherence is kept
along typed code and under labels (`coh_of_tmor`, `coh_initLocals`, `coh_withLabel`), so a whole
typed program needs it only at its entry, and every state a typed interface describes makes it
hold (`realizes_coh`: from `StoreOk`, `FrameOk`'s `ModuleInstOk` and `Ctx.Good`). Nothing is left
as a premise: for `call_indirect`/`call_ref` the checker reads only the annotation's counts, which
typing fixes; the callee resolved at run time is the run's business (`EvalOXP` records its counts).

**B.1. The typed frame rule** (`tmor_frame`): typed code is typed with valid extra value types
`R` below its stack, by Core's `Instrs_ok/frame` and the check's stability under a higher stack
(`chkE_shift`).

**B.2. Arity respect from typed answers.** `arityResp_of_typedAns`: an oracle whose answers keep
`Γ` and return values of the callee's result types respects arities, so the answered tensor holds
for typed code under it with no further premise (`tmor_tensor_typedAns`). The closure:
`closedCallXP_funcs` (the closure keeps the store's functions) and `arityResp_fitClosed` (the
closure on calls passing the callee's parameter count, `fitP closedCallXP`, respects arities, by
its Core 3.0 soundness `PendSim.closedCallXP_sound`), so `tmor_tensor_fitClosed`. The fit premise
is the minimal one: the soundness is stated for that parameter count, and an `ArityResp` oracle
is asked to answer every argument list; checked code calls with exactly the parameter count, but
transporting runs between `closedCallXP` and `fitP closedCallXP` needs the arity invariant itself
and is not proved here.

**B.3. Strength.** The relations of answered runs form a category (`seqR_idR_left`,
`seqR_idR_right`, `seqR_assoc`) into which code denotes functorially (`denR_nil`, `denR_append`).
The whiskering is unital and associative in the passive stack (`whiskR_nil`, `whiskR_append`),
preserves composition (`whiskR_seqR`) and identities (`whiskR_idR`, `whiskR_denR_nil`). On typed
code under an arity-respecting oracle, at a typed state, the runs on `stk ++ rest` read at the
targets' arities are the whiskered runs (`tmor_tensorR`), and for a composite they are the
composite of the whiskered runs (`tmor_tensorR_comp`).

**B.4. Premonoidal, not monoidal.** `leftR n g` (`g ⋉ -`, the whiskering code has) and
`rightR m g` (`- ⋊ g`, semantic only) give the two whiskerings; `Interchange` is the interchange
law. Pure morphisms (`PureAt`: total, effect-free stack functions independent of store and frame)
are central (`interchange_of_pure`); the identity and integer constants are pure (`pureAt_nil`,
`pureAt_intConst`). The interchange law fails for calls (`not_interchange`): a coherent typed
interface, a typed state, two typed endomorphisms `call 0`, `call 1` of the empty stack and an
oracle with typed answers recording its calls in the store, where the two orders reach different
stores. Only these laws are proved; no premonoidal functor is stated.
-/

public section

namespace Silmaril.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Abstract.CallXT (typeArity)

variable {H : Type} {Γ : Ctx H} {C : Abstract.CallRel H}

/-! ## A. Arities from coherence -/

theorem callArity_of_coh {I : TIface} (hco : Coh Γ I) {x : FuncIdx} {d : DefType}
    {ps rs : Ty (.list .val)} (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs)) :
    callArity Γ.funcs I.mi x = some (ps.toList.length, rs.toList.length) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.callArity_of_coh hco hf he

theorem typeArity_of_coh {I : TIface} (hco : Coh Γ I) {y : TypeIdx} {d : DefType}
    {ps rs : Ty (.list .val)} (hd : I.C.type? y = some d) (he : Expand d (.func ps rs)) :
    typeArity I.mi y = some (ps.toList.length, rs.toList.length) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.typeArity_of_coh hco hd he

theorem tagFields_of_coh {I : TIface} (hco : Coh Γ I) {x : TagIdx} {d : DefType}
    {ts : Ty (.list .val)} (hx : I.C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil)) :
    tagFields Γ.tags I.mi x = some ts.toList.length :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tagFields_of_coh hco hx he

/-- **The clauses of a typed `try_table`** push values the checker reads, accepted at their
labels. -/
theorem clauses_of_coh {I : TIface} (hco : Coh Γ I) :
    ∀ {cs : List Catch}, (∀ c ∈ cs, CatchOk I.C c) →
      ∃ ns, cs.mapM (clauseCount Γ.tags I.mi) = some ns ∧
        catchOk (I.C.labels.map List.length) cs ns = true :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.clauses_of_coh hco

/-! ## A. Coherence along typed code, and at typed states -/

theorem coh_initLocals {I : TIface} (hco : Coh Γ I) (xs : List Nat) (ts : List CValType) :
    Coh Γ ⟨I.mi, I.C.initLocals xs, ts⟩ :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.coh_initLocals hco xs ts

theorem coh_withLabel {I : TIface} (hco : Coh Γ I) (L ts : List CValType) :
    Coh Γ ⟨I.mi, I.C.withLabel L, ts⟩ :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.coh_withLabel hco L ts

theorem coh_of_tmor {I J : TIface} {ft : Bool} {es : List BExpr} (h : TMor Γ I J ft es)
    (hco : Coh Γ I) : Coh Γ J :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.coh_of_tmor h hco

/-- **Typed states are coherent.** -/
theorem realizes_coh {I : TIface} {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) : Coh Γ I :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.realizes_coh hr

/-! ## A. The closure with the premises discharged -/

theorem thom_block {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hco : Coh Γ I)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.block bt body] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_block hco hts hpre hbt hb hJ

theorem thom_loop {I J : TIface} {bt : BlockType} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hco : Coh Γ I)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₁, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.loop bt body] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_loop hco hts hpre hbt hb hJ

theorem thom_if {I K J₁ J₂ : TIface} {bt : BlockType} {c t el : List BExpr}
    {pre t₁ t₂ : List CValType} {ft₁ ft₂ : Bool} (hco : Coh Γ I) (hc : THom Γ I K c)
    (hts : K.ts = pre ++ t₁ ++ [.i32])
    (hpre : ResultOk K.C.toTypeCtx pre) (hbt : BlockTypeOk K.C bt t₁ t₂)
    (ht : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₁ ft₁ t) (hJ₁ : J₁.ts = t₂)
    (he : TMor Γ ⟨I.mi, K.C.withLabel t₂, t₁⟩ J₂ ft₂ el) (hJ₂ : J₂.ts = t₂) :
    THom Γ I ⟨I.mi, K.C, pre ++ t₂⟩ [.if_ bt c t el] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_if hco hc hts hpre hbt ht hJ₁ he hJ₂

theorem thom_try {I J : TIface} {bt : BlockType} {cs : List Catch} {body : List BExpr}
    {pre t₁ t₂ : List CValType} {ft : Bool} (hco : Coh Γ I)
    (hts : I.ts = pre ++ t₁) (hpre : ResultOk I.C.toTypeCtx pre) (hbt : BlockTypeOk I.C bt t₁ t₂)
    (hcok : ∀ c ∈ cs, CatchOk I.C c)
    (hb : TMor Γ ⟨I.mi, I.C.withLabel t₂, t₁⟩ J ft body) (hJ : J.ts = t₂) :
    THom Γ I ⟨I.mi, I.C, pre ++ t₂⟩ [.tryTable bt cs body] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_try hco hts hpre hbt hcok hb hJ

theorem thom_call {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hco : Coh Γ I) (hts : I.ts = pre ++ ps.toList)
    (hpre : ResultOk I.C.toTypeCtx pre)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.call x) []] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_call hco hts hpre hf he

theorem thom_callIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType} {l : Limits}
    {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)} {pre : List CValType}
    (hco : Coh Γ I)
    (hts : I.ts = pre ++ (ps.toList ++ [a.valType])) (hpre : ResultOk I.C.toTypeCtx pre)
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hs : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callIndirect x y) []] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_callIndirect hco hts hpre ht hs hd he

theorem thom_callRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {pre : List CValType} (hco : Coh Γ I)
    (hts : I.ts = pre ++ (ps.toList ++ [.refT true (.defHeap d)]))
    (hpre : ResultOk I.C.toTypeCtx pre) (hd : I.C.type? y = some d) (he : Expand d (.func ps rs)) :
    THom Γ I ⟨I.mi, I.C, pre ++ rs.toList⟩ [.op (.callRef y) []] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_callRef hco hts hpre hd he

theorem tstop_returnCall {I : TIface} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hco : Coh Γ I) (hts : I.ts = t₃ ++ ps.toList)
    (hf : I.C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCall x) []] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tstop_returnCall hco hts hf he hr hs hok

theorem tstop_returnCallIndirect {I : TIface} {x : TableIdx} {y : TypeIdx} {a : AddrType}
    {l : Limits} {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hco : Coh Γ I) (hts : I.ts = t₃ ++ ps.toList ++ [a.valType])
    (ht : I.C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hsub : Sub I.C.toTypeCtx rt Ty.funcref)
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallIndirect x y) []] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tstop_returnCallIndirect hco hts ht hsub hd he hr hs hok

theorem tstop_returnCallRef {I : TIface} {y : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
    {rs' t₃ t₄ : List CValType} (hco : Coh Γ I)
    (hts : I.ts = t₃ ++ ps.toList ++ [.refT true (.defHeap d)])
    (hd : I.C.type? y = some d) (he : Expand d (.func ps rs))
    (hr : I.C.return_ = some rs') (hs : ResultSub I.C.toTypeCtx rs.toList rs')
    (hok : InstrTypeOk I.C (.plain t₃ t₄)) :
    TStop Γ I ⟨I.mi, I.C, t₄⟩ [.op (.returnCallRef y) []] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tstop_returnCallRef hco hts hd he hr hs hok

theorem tstop_throw {I : TIface} {x : TagIdx} {d : DefType} {ts : Ty (.list .val)}
    {t₁ t₂ : List CValType} (hco : Coh Γ I) (hts : I.ts = t₁ ++ ts.toList)
    (hx : I.C.tags[x.toNat]? = some d)
    (he : Expand d (.func ts .nil)) (hok : InstrTypeOk I.C (.plain t₁ t₂)) :
    TStop Γ I ⟨I.mi, I.C, t₂⟩ [.op (.throw x) []] :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tstop_throw hco hts hx he hok

/-! ## B.1. The typed frame rule -/

section Shift

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat}

/-- **The check is stable under a higher stack.** -/
theorem chkE_shift (k : Nat) :
    ∀ (h : Nat) (es : List BExpr) {o : Option Nat},
      chkE ext F mi nl ret labels (some h) es = some o →
        chkE ext F mi nl ret labels (some (h + k)) es = some (o.map (· + k)) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.chkE_shift k

end Shift

/-- **The typed frame rule**: typed code is typed with extra value types below its stack. -/
theorem tmor_frame {Γ : Ctx H} {I J : TIface} {ft : Bool} {es : List BExpr}
    (h : TMor Γ I J ft es) {R : List CValType} (hR : ResultOk I.C.toTypeCtx R) :
    TMor Γ (I.withBelow R) (J.withBelow R) ft es :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tmor_frame h hR

/-! ## B.2. Arity respect from typed answers -/

/-- **Typed answers respect arities.** -/
theorem arityResp_of_typedAns {Γ : Ctx H} {C : Abstract.CallRel H} (h : TypedAns Γ C) :
    ArityResp Γ C :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.arityResp_of_typedAns h

/-- **The closure keeps the store's functions.** -/
theorem closedCallXP_funcs :
    ∀ (s : Store H) a us out, closedCallXP s a us out → out.1.funcs = s.funcs :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.closedCallXP_funcs

/-- **The closure on fitting calls respects arities.** -/
theorem arityResp_fitClosed (Γ : Ctx H) : ArityResp Γ (fitP closedCallXP) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.arityResp_fitClosed Γ

/-- **The answered tensor for typed code under typed answers**, no further premise. -/
theorem tmor_tensor_typedAns (hC : TypedAns Γ C) {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP C s f (stk ++ rest) es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X :=
  ExposePTyped.tmor_tensor (arityResp_of_typedAns hC) hm hr rest s' f' X

/-- **The answered tensor for typed code under the closure on fitting calls.** -/
theorem tmor_tensor_fitClosed {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    (∃ o', EvalOXP (fitP closedCallXP) s f (stk ++ rest) es (s', f', o') ∧
        trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP (fitP closedCallXP) s f stk es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X :=
  ExposePTyped.tmor_tensor (arityResp_fitClosed Γ) hm hr rest s' f' X

/-! ## B.3. The category of answered runs and the strength -/

theorem seqR_idR_left (g : ORel H) : seqR idR g = g :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.seqR_idR_left g

theorem seqR_idR_right (g : ORel H) : seqR g idR = g :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.seqR_idR_right g

theorem seqR_assoc (g₁ g₂ g₃ : ORel H) : seqR (seqR g₁ g₂) g₃ = seqR g₁ (seqR g₂ g₃) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.seqR_assoc g₁ g₂ g₃

theorem denR_nil : denR C [] = idR :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.denR_nil

theorem denR_append (es₁ es₂ : List BExpr) :
    denR C (es₁ ++ es₂) = seqR (denR C es₁) (denR C es₂) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.denR_append es₁ es₂

theorem whiskR_nil (g : ORel H) : whiskR [] g = g :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.whiskR_nil g

theorem whiskR_append (R₁ R₂ : List Val) (g : ORel H) :
    whiskR (R₁ ++ R₂) g = whiskR R₂ (whiskR R₁ g) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.whiskR_append R₁ R₂ g

theorem whiskR_seqR (R : List Val) (g₁ g₂ : ORel H) :
    whiskR R (seqR g₁ g₂) = seqR (whiskR R g₁) (whiskR R g₂) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.whiskR_seqR R g₁ g₂

theorem whiskR_idR (R : List Val) {s : Store H} {f : Frame} {stk' : List Val} {s' : Store H}
    {f' : Frame} {o : POut} :
    whiskR R idR s f stk' s' f' o ↔ (∃ stk, stk' = stk ++ R) ∧ idR s f stk' s' f' o :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.whiskR_idR R

/-- **The answered tensor, relationally**: on typed code at a typed state, the runs on a stack
with a passive suffix are the whiskered runs, read at the targets' arities. -/
theorem tmor_tensorR (hC : ArityResp Γ C) {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C es) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (whiskR rest (denR C es)) s f (stk ++ rest) s' f' X :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tmor_tensorR hC hm hr rest s' f' X

/-- **Whiskering preserves composition** on typed code. -/
theorem tmor_tensorR_comp (hC : ArityResp Γ C) {I J K : TIface} {ft : Bool}
    {es₁ es₂ : List BExpr} (h₁ : THom Γ I J es₁) (h₂ : TMor Γ J K ft es₂) {s : Store H}
    {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H)
    (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C (es₁ ++ es₂)) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (seqR (whiskR rest (denR C es₁)) (whiskR rest (denR C es₂)))
        s f (stk ++ rest) s' f' X :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.tmor_tensorR_comp hC h₁ h₂ hr rest s' f' X

/-- **Whiskering preserves the identity.** -/
theorem whiskR_denR_nil (rest : List Val) (s : Store H) (f : Frame) (stk : List Val)
    (s' : Store H) (f' : Frame) (o : POut) :
    whiskR rest (denR C []) s f (stk ++ rest) s' f' o ↔ idR s f (stk ++ rest) s' f' o :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.whiskR_denR_nil rest s f stk s' f' o

/-! ## B.4. Premonoidal, not monoidal -/

section Pure

variable {n n' : Nat} {φ : List Val → List Val} {g₁ : ORel H}

/-- **Pure morphisms are central.** -/
theorem interchange_of_pure (hp : PureAt n n' φ g₁) (g₂ : ORel H) : Interchange n n' g₁ g₂ :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.interchange_of_pure hp g₂

end Pure

theorem pureAt_nil {C : Abstract.CallRel H} (n : Nat) : PureAt n n id (denR C []) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.pureAt_nil n

theorem pureAt_intConst {C : Abstract.CallRel H} (t : IntType) (b : BitVec t.width) :
    PureAt 0 1 (fun _ => [ofInt t b]) (denR C [.op (.intConst t b) []]) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.pureAt_intConst t b

/-- **The interchange law fails for typed calls.** -/
theorem not_interchange :
    ∃ (Γ : Ctx Unit) (C : Abstract.CallRel Unit) (I : TIface) (e₁ e₂ : List BExpr)
      (s : Store Unit) (f : Frame),
      TypedAns Γ C ∧ ArityResp Γ C ∧ Coh Γ I ∧ THom Γ I I e₁ ∧ THom Γ I I e₂ ∧
        Realizes Γ I s f [] ∧
        (∃ s' f' o, seqR (leftR 0 (denR C e₁)) (rightR 0 (denR C e₂)) s f [] s' f' o ∧
          ¬ seqR (rightR 0 (denR C e₂)) (leftR 0 (denR C e₁)) s f [] s' f' o) ∧
        ¬ Interchange 0 0 (denR C e₁) (denR C e₂) :=
  Silmaril.Proofs.Wasm.Abstract.TypedCat.Ex.not_interchange

end Silmaril.Wasm.Abstract.TypedCat
