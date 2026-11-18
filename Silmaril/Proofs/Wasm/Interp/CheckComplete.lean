module

public import Silmaril.Wasm.Interp.CheckComplete.Defs
public import Silmaril.Proofs.Wasm.Interp.EHExt
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Abstract.TypedCatValid.Thms
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall
public import Silmaril.Wasm.Execution.Core.Soundness.CallMeta

/-!
Proofs for `Silmaril.Wasm.Interp.CheckComplete.Thms`.

The invariant is `Good es a b`: from every height `a + k` the check of `es` succeeds, never
falling through or falling through at `b + k`. It holds for the empty sequence (`a = b`), is
closed under concatenation (`good_append`), under a frame (`good_frame`) and under equal counts,
so it follows `Instrs_ok`'s rules (`good_instrs`). For one instruction (`good_instr`) it is read
off `Instr_ok` and the context match: every supported instruction pops and pushes the counts of
its instruction type, every branch target, local, block type, callee and tag the checker reads
exists with the counts the context gives it. Bodies are handled by induction on the size of the
instructions (`good_lt`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Interp.CheckComplete

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Interp.CheckComplete
open Silmaril.Wasm.Validation (Context InstrOk InstrsOk InstrType BlockTypeOk CatchOk Expand
  DefType ResultSub ExprOk)
open Silmaril.Wasm.Abstract.CallXT (typeArity)

variable {H : Type}

/-! ## The profile -/

theorem supported_append : ∀ (a b : List BExpr),
    supported (a ++ b) = (supported a && supported b)
  | [], _ => by simp [supported]
  | e :: a, b => by simp [supported, supported_append a b, Bool.and_assoc]

/-! ## Function types -/

theorem funcType_of_expand {d : DefType} {ps rs : Validation.Ty (.list .val)}
    (he : Expand d (.func ps rs)) : DefType.funcType? d = some (ps.toList, rs.toList) := by
  unfold DefType.funcType?
  rw [Expand.iff.mp he]

theorem expand_of_funcType {d : DefType} {p r : List Validation.CValType}
    (h : DefType.funcType? d = some (p, r)) :
    ∃ ps rs, Expand d (.func ps rs) ∧ ps.toList = p ∧ rs.toList = r := by
  unfold DefType.funcType? at h
  split at h
  · rename_i ps rs he
    cases h
    exact ⟨ps, rs, Expand.iff.mpr he, rfl, rfl⟩
  · cases h

/-! ## The checker on sequences -/

section Seq

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat}

theorem chkE_append : ∀ (oh : Option Nat) (es₁ es₂ : List BExpr),
    chkE ext F mi nl ret labels oh (es₁ ++ es₂) =
      (chkE ext F mi nl ret labels oh es₁).bind fun o => chkE ext F mi nl ret labels o es₂
  | none, es₁, es₂ => by simp
  | some h, [], es₂ => by simp
  | some h, e :: es₁, es₂ => by
    simp only [List.cons_append, chkE, Option.bind_assoc]
    congr 1
    funext o
    exact chkE_append o es₁ es₂

/-- **The invariant**: from every height `a + k`, the check of `es` succeeds, never falling
through or falling through at `b + k`. -/
def Good (ext : ExtArity H) (F : List (FuncInst H)) (mi : ModuleInst) (nl ret : Nat)
    (labels : List Nat) (es : List BExpr) (a b : Nat) : Prop :=
  ∀ k, ∃ o, chkE ext F mi nl ret labels (some (a + k)) es = some o ∧ (o = none ∨ o = some (b + k))

theorem good_nil {a : Nat} : Good ext F mi nl ret labels [] a a :=
  fun k => ⟨some (a + k), rfl, .inr rfl⟩

theorem good_append {es₁ es₂ : List BExpr} {a b c : Nat}
    (g₁ : Good ext F mi nl ret labels es₁ a b) (g₂ : Good ext F mi nl ret labels es₂ b c) :
    Good ext F mi nl ret labels (es₁ ++ es₂) a c := by
  intro k
  obtain ⟨o, h₁, ho⟩ := g₁ k
  rw [chkE_append, h₁]
  rcases ho with rfl | rfl
  · exact ⟨none, by simp, .inl rfl⟩
  · simpa using g₂ k

theorem good_frame {es : List BExpr} {a b : Nat} (m : Nat)
    (g : Good ext F mi nl ret labels es a b) : Good ext F mi nl ret labels es (m + a) (m + b) := by
  intro k
  have := g (m + k)
  rw [show m + a + k = a + (m + k) by omega, show m + b + k = b + (m + k) by omega]
  exact this

theorem good_single {e : BExpr} {a b : Nat}
    (h : ∀ k, ∃ o, chk1E ext F mi nl ret labels (a + k) e = some o ∧
      (o = none ∨ o = some (b + k))) : Good ext F mi nl ret labels [e] a b := by
  intro k
  obtain ⟨o, h₁, ho⟩ := h k
  refine ⟨o, ?_, ho⟩
  simp only [chkE, h₁, Option.bind_some]
  rcases o with _ | _ <;> rfl

theorem good_op {i : Instr} {e : BExpr} (he : e = .op i []) {a b : Nat}
    (h : ∀ k, ∃ o, flatChkE ext F mi nl ret labels (a + k) i = some o ∧
      (o = none ∨ o = some (b + k))) : Good ext F mi nl ret labels [e] a b := by
  subst he
  exact good_single h

end Seq

/-! ## The context match -/

section Match

variable {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat} {C : Context}

theorem ctxMatch_withLabel (hm : CtxMatch tags F mi nl ret labels C) (ts : List Validation.CValType) :
    CtxMatch tags F mi nl ret (ts.length :: labels) (C.withLabel ts) :=
  ⟨by simp [Context.withLabel, hm.labels], hm.ret, hm.locals, hm.types, hm.funcs, hm.tags⟩

theorem ctxMatch_initLocals (hm : CtxMatch tags F mi nl ret labels C) (xs : List Nat) :
    CtxMatch tags F mi nl ret labels (C.initLocals xs) := by
  have hloc : ∀ (x : Nat) (lt : Validation.LocalType), (C.initLocals xs).locals[x]? = some lt →
      x < nl := fun x lt h => by
    obtain ⟨lt', h'⟩ := Context.initLocals_exists.1 ⟨lt, h⟩
    exact hm.locals x lt' h'
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs
  rw [hL] at hloc ⊢
  exact ⟨hm.labels, hm.ret, hloc, hm.types, hm.funcs, hm.tags⟩

theorem blockArity_of_ok (hm : CtxMatch tags F mi nl ret labels C) {bt : BlockType}
    {t₁ t₂ : List Validation.CValType} (h : BlockTypeOk C bt t₁ t₂) :
    blockArity mi bt = some (t₁.length, t₂.length) := by
  cases h with
  | empty => rfl
  | value _ => rfl
  | typeIdx hd he =>
    have hd' := hd
    simp only [Context.type?, hm.types] at hd'
    simp [blockArity, Binaryen.arity, Frame.type?, hd', funcType_of_expand he]

theorem typeArity_of_ok (hm : CtxMatch tags F mi nl ret labels C) {y : TypeIdx} {d : DefType}
    {ps rs : Validation.Ty (.list .val)} (hd : C.type? y = some d) (he : Expand d (.func ps rs)) :
    typeArity mi y = some (ps.toList.length, rs.toList.length) := by
  have hd' := hd
  simp only [Context.type?, hm.types] at hd'
  simp [typeArity, hd', funcType_of_expand he]

theorem labels_get (hm : CtxMatch tags F mi nl ret labels C) {l : LabelIdx}
    {ts : List Validation.CValType} (hl : C.labels[l.toNat]? = some ts) :
    labels[l.toNat]? = some ts.length := by
  rw [hm.labels, List.getElem?_map, hl]
  rfl

theorem catchOk_cons {cs : List Catch} {ns : List Nat} {c : Catch} {n m : Nat}
    (hl : labels[(catchLabel c).toNat]? = some m) (hle : m ≤ n) (h : catchOk labels cs ns = true) :
    catchOk labels (c :: cs) (n :: ns) = true := by
  simp only [catchOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h ⊢
  refine ⟨by simp [h.1], ?_⟩
  intro p hp
  simp only [List.zip_cons_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · simp [hl, hle]
  · exact h.2 p hp

theorem clause_ok (hm : CtxMatch tags F mi nl ret labels C) {c : Catch} (h : CatchOk C c) :
    ∃ n m, clauseCount tags mi c = some n ∧ labels[(catchLabel c).toNat]? = some m ∧ m ≤ n := by
  cases h with
  | catch_ hx he hl hs =>
    refine ⟨_, _, hm.tags _ _ _ hx he, labels_get hm hl, ?_⟩
    rw [hs.length_eq]
  | @catchRef x l d ts lt hx he hl hs =>
    refine ⟨ts.toList.length + 1, lt.length, by simp [clauseCount, hm.tags _ _ _ hx he], labels_get hm hl, ?_⟩
    have := hs.length_eq
    simp at this
    omega
  | catchAll hl hs =>
    refine ⟨0, _, rfl, labels_get hm hl, ?_⟩
    have := hs.length_eq
    simp at this
    omega
  | catchAllRef hl hs =>
    refine ⟨1, _, rfl, labels_get hm hl, ?_⟩
    have := hs.length_eq
    simp at this
    omega

theorem catches_ok (hm : CtxMatch tags F mi nl ret labels C) :
    ∀ (cs : List Catch), (∀ c ∈ cs, CatchOk C c) →
      ∃ ns, cs.mapM (clauseCount tags mi) = some ns ∧ catchOk labels cs ns = true
  | [], _ => ⟨[], rfl, rfl⟩
  | c :: cs, h => by
    obtain ⟨ns, h₁, h₂⟩ := catches_ok hm cs fun c hc => h c (List.mem_cons_of_mem _ hc)
    obtain ⟨n, m, hn, hl, hle⟩ := clause_ok hm (h c List.mem_cons_self)
    exact ⟨n :: ns, by simp [List.mapM_cons, hn, h₁], catchOk_cons hl hle h₂⟩

end Match

/-! ## Typed module instances -/

section Module

variable {s : Store H} {mi : ModuleInst} {C : Context}

/-- A function of a typed store has a function type. -/
theorem funcType_of_storeOk (hs : StoreOk s) {a : Nat} {fi : FuncInst H}
    (hfi : s.funcs[a]? = some fi) : ∃ ps rs, Expand fi.type (.func ps rs) := by
  have hfo := hs.funcs fi (List.mem_of_getElem? hfi)
  cases hfo with
  | host _ he _ => exact ⟨_, _, he⟩
  | wasm _ _ hcode =>
    obtain ⟨C, ps, rs, lts, hb⟩ := Abstract.TypedCatValid.bodyOk_of_storeOk hs hfi hcode
    obtain ⟨ps₀, rs₀, hty, -, -⟩ := Abstract.TypedCatValid.bodyOk_funcType hs hfi hb
    obtain ⟨P, R, he, -, -⟩ := expand_of_funcType hty
    exact ⟨P, R, he⟩

/-- **The callees of a typed module instance have their context counts.** -/
theorem callArity_of_moduleInstOk (hs : StoreOk s) (hmi : ModuleInstOk s mi C) {x : FuncIdx}
    {d : DefType} {ps rs : Validation.Ty (.list .val)} (hd : C.funcs[x.toNat]? = some d)
    (he : Expand d (.func ps rs)) :
    callArity s.funcs mi x = some (ps.toList.length, rs.toList.length) := by
  cases hmi with
  | mk _ _ _ hfuncs =>
    obtain ⟨a, ha, hx⟩ := forall₂_getElem?_right hfuncs hd
    obtain ⟨fi, hfi⟩ := ExternAddrOk.func_inv hx
    have hlen : ∃ p r, DefType.funcType? fi.type = some (p, r) ∧ p.length = ps.toList.length ∧
        r.length = rs.toList.length := by
      rcases PC.externAddr_func hx rfl hfi rfl with rfl | ⟨hdok, hsub⟩
      · exact ⟨_, _, funcType_of_expand he, rfl, rfl⟩
      · obtain ⟨P, R, he'⟩ := funcType_of_storeOk hs hfi
        obtain ⟨hp, hr⟩ := PC.ds_func (PC.StoreOk.func_tyOk hs hfi) hdok (.defDef hsub) he' he
        exact ⟨_, _, funcType_of_expand he', hp.length_eq.symm, hr.length_eq⟩
    obtain ⟨p, r, hpr, hp, hr⟩ := hlen
    simp [callArity, ha, hfi, hpr, hp, hr]

/-- **The tags of a typed module instance have their context field counts.** -/
theorem tagFields_of_moduleInstOk (hs : StoreOk s) (hmi : ModuleInstOk s mi C) {x : TagIdx}
    {d : DefType} {ts : Validation.Ty (.list .val)} (hd : C.tags[x.toNat]? = some d)
    (he : Expand d (.func ts .nil)) : tagFields s.tags mi x = some ts.toList.length := by
  cases hmi with
  | mk _ htags =>
    obtain ⟨a, ha, hx⟩ := forall₂_getElem?_right htags hd
    obtain ⟨ti, hti, hte⟩ := ExternAddrOk.tag_inv hs hx
    cases hte
    have := funcType_of_expand he
    simp [tagFields, ha, hti, this]

/-- **The checker's parameters for a function body read its `Func_ok` body context.** -/
theorem ctxMatch_funcBody (hs : StoreOk s) (hmi : ModuleInstOk s mi C)
    {ps rs : List Validation.CValType} {lts : List Validation.LocalType} {nl : Nat}
    (hnl : nl = ps.length + lts.length) :
    CtxMatch s.tags s.funcs mi nl rs.length [rs.length] (C.funcBody ps rs lts) := by
  obtain ⟨-, -, -, htypes⟩ := ModuleInstOk.ctx_fields hmi
  refine ⟨rfl, ?_, ?_, htypes, fun x d ps rs hd he => callArity_of_moduleInstOk hs hmi hd he,
    fun x d ts hd he => tagFields_of_moduleInstOk hs hmi hd he⟩
  · intro ts h
    simp only [Context.funcBody, Option.some.injEq] at h
    rw [h]
  · intro x lt h
    have := (List.getElem?_eq_some_iff.1 h).1
    simp only [Context.funcBody, List.length_append, List.length_map] at this
    omega

end Module

/-! ## Completeness -/

section Complete

variable {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}

/-- `Good` follows `Instrs_ok`'s rules, given it for single instructions. -/
theorem good_instrs {S : Instr → Prop}
    (hI : ∀ {C : Context} {i : Instr} {it : InstrType} {nl ret : Nat} {labels : List Nat},
      InstrOk C i it → S i → supported1 (liftInstr i) = true →
        CtxMatch tags F mi nl ret labels C →
          Good (ehExt tags) F mi nl ret labels [liftInstr i] it.params.length it.results.length) :
    ∀ {C : Context} {is : List Instr} {it : InstrType}, InstrsOk C is it → (∀ i ∈ is, S i) →
      supported (liftInstrs is) = true → ∀ {nl ret : Nat} {labels : List Nat},
        CtxMatch tags F mi nl ret labels C →
          Good (ehExt tags) F mi nl ret labels (liftInstrs is) it.params.length
            it.results.length := by
  intro C is it h
  induction h using InstrsOk.ind with
  | nil => intro _ _ _ _ _ _; exact good_nil
  | instr h =>
    intro hS hs nl ret labels hm
    exact hI h (hS _ (List.mem_singleton_self _)) (by simpa [liftInstrs, supported] using hs) hm
  | seq h₁ hx h₂ ih₁ ih₂ =>
    intro hS hs nl ret labels hm
    rw [liftInstrs_append, supported_append, Bool.and_eq_true] at hs
    rw [liftInstrs_append]
    exact good_append (ih₁ (fun i hi => hS i (List.mem_append_left _ hi)) hs.1 hm)
      (ih₂ (fun i hi => hS i (List.mem_append_right _ hi)) hs.2 (ctxMatch_initLocals hm _))
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs' ih =>
    intro hS hs nl ret labels hm
    simp only [liftInstrs, supported, Bool.and_eq_true] at hs
    have g₁ := hI hi (hS i List.mem_cons_self) hs.1 hm
    have g₂ := ih (fun j hj => hS j (List.mem_cons_of_mem _ hj)) hs.2 (ctxMatch_initLocals hm xs₁)
    exact good_append (es₁ := [liftInstr i]) g₁ g₂
  | sub h hsub hok ih =>
    intro hS hs nl ret labels hm
    rw [hsub.1.length_eq, ← hsub.2.1.length_eq]
    exact ih hS hs hm
  | @frame C is ts t₁ t₂ xs h hok ih =>
    intro hS hs nl ret labels hm
    have := good_frame ts.length (ih hS hs hm)
    simpa only [List.length_append] using this

theorem xInstr_of_flat {i : Instr} (hst : structuredInstr i = false)
    (hsup : supported1 (liftInstr i) = true) : XProfile.xInstr i = true := by
  rw [liftInstr_flat hst] at hsup
  simpa [supported1, supported] using hsup

/-- **`Good` for one supported, typed instruction**, given it for the bodies of smaller
instructions. -/
theorem good_instr {n : Nat}
    (IH : ∀ {C : Context} {is : List Instr} {it : InstrType}, InstrsOk C is it →
      (∀ i ∈ is, sizeOf i < n) → supported (liftInstrs is) = true →
      ∀ {nl ret : Nat} {labels : List Nat}, CtxMatch tags F mi nl ret labels C →
        Good (ehExt tags) F mi nl ret labels (liftInstrs is) it.params.length it.results.length)
    {C : Context} {i : Instr} {it : InstrType} {nl ret : Nat} {labels : List Nat}
    (hi : InstrOk C i it) (hsz : sizeOf i < n + 1) (hsup : supported1 (liftInstr i) = true)
    (hm : CtxMatch tags F mi nl ret labels C) :
    Good (ehExt tags) F mi nl ret labels [liftInstr i] it.params.length it.results.length := by
  cases hi with
  | parametric h =>
    cases h <;> refine good_op rfl fun k => ?_ <;> simp [flatChkE, flatEff] <;> omega
  | numeric h =>
    cases h <;> (have hx := xInstr_of_flat rfl hsup; first
      | (simp [XProfile.xInstr] at hx; done)
      | (refine good_op rfl fun k => ?_; simp [flatChkE, flatEff, Nat.add_comm]))
  | vector h => cases h <;> (have hx := xInstr_of_flat rfl hsup; simp [XProfile.xInstr] at hx)
  | «variable» h =>
    cases h with
    | localSet h =>
      refine good_op rfl fun k => ?_; simp [flatChkE, flatEff, hm.locals _ _ h]
    | localTee h =>
      refine good_op rfl fun k => ?_; simp [flatChkE, flatEff, hm.locals _ _ h]; omega
    | localGet _ => refine good_op rfl fun k => ?_; simp [flatChkE, flatEff]; omega
    | globalGet _ => refine good_op rfl fun k => ?_; simp [flatChkE, flatEff]; omega
    | globalSet _ => refine good_op rfl fun k => ?_; simp [flatChkE, flatEff]
  | memory h =>
    cases h <;> (have hx := xInstr_of_flat rfl hsup; first
      | (simp [XProfile.xInstr] at hx; done)
      | (refine good_op rfl fun k => ?_; simp [flatChkE, flatEff, Nat.add_comm]))
  | table h => cases h <;> (have hx := xInstr_of_flat rfl hsup; simp [XProfile.xInstr] at hx)
  | reference h => cases h <;> (have hx := xInstr_of_flat rfl hsup; simp [XProfile.xInstr] at hx)
  | @block C bt body t₁ t₂ xs hbt hb =>
    have hs' : supported (liftInstrs body) = true := by simpa [liftInstr, supported1] using hsup
    obtain ⟨o, hc, ho⟩ := IH hb (fun j hj => by
      have := List.sizeOf_lt_of_mem hj
      simp only [Instr.block.sizeOf_spec] at hsz
      omega) hs' (ctxMatch_withLabel hm t₂) 0
    have he : endsAt (chkE (ehExt tags) F mi nl ret (t₂.length :: labels) (some t₁.length)
        (liftInstrs body)) t₂.length = true := by
      simp only [Nat.add_zero] at hc ho
      rw [hc]; rcases ho with rfl | rfl <;> simp [endsAt]
    refine good_single fun k => ⟨some (t₂.length + k), ?_, .inr rfl⟩
    simp [liftInstr, chk1E, blockArity_of_ok hm hbt, he]
    omega
  | @loop C bt body t₁ t₂ xs hbt hb =>
    have hs' : supported (liftInstrs body) = true := by simpa [liftInstr, supported1] using hsup
    obtain ⟨o, hc, ho⟩ := IH hb (fun j hj => by
      have := List.sizeOf_lt_of_mem hj
      simp only [Instr.loop.sizeOf_spec] at hsz
      omega) hs' (ctxMatch_withLabel hm t₁) 0
    have he : endsAt (chkE (ehExt tags) F mi nl ret (t₁.length :: labels) (some t₁.length)
        (liftInstrs body)) t₂.length = true := by
      simp only [Nat.add_zero] at hc ho
      rw [hc]; rcases ho with rfl | rfl <;> simp [endsAt]
    refine good_single fun k => ⟨some (t₂.length + k), ?_, .inr rfl⟩
    simp [liftInstr, chk1E, blockArity_of_ok hm hbt, he]
    omega
  | @if_ C bt b₁ b₂ t₁ t₂ xs₁ xs₂ hbt h₁ h₂ =>
    have hs' : supported (liftInstrs b₁) = true ∧ supported (liftInstrs b₂) = true := by
      simpa [liftInstr, supported1, supported] using hsup
    simp only [Instr.if_.sizeOf_spec] at hsz
    obtain ⟨o₁, hc₁, ho₁⟩ := IH h₁ (fun j hj => by
      have := List.sizeOf_lt_of_mem hj
      omega) hs'.1 (ctxMatch_withLabel hm t₂) 0
    obtain ⟨o₂, hc₂, ho₂⟩ := IH h₂ (fun j hj => by
      have := List.sizeOf_lt_of_mem hj
      omega) hs'.2 (ctxMatch_withLabel hm t₂) 0
    have he₁ : endsAt (chkE (ehExt tags) F mi nl ret (t₂.length :: labels) (some t₁.length)
        (liftInstrs b₁)) t₂.length = true := by
      simp only [Nat.add_zero] at hc₁ ho₁
      rw [hc₁]; rcases ho₁ with rfl | rfl <;> simp [endsAt]
    have he₂ : endsAt (chkE (ehExt tags) F mi nl ret (t₂.length :: labels) (some t₁.length)
        (liftInstrs b₂)) t₂.length = true := by
      simp only [Nat.add_zero] at hc₂ ho₂
      rw [hc₂]; rcases ho₂ with rfl | rfl <;> simp [endsAt]
    refine good_single fun k => ⟨some (t₂.length + k), ?_, .inr rfl⟩
    simp [liftInstr, chk1E, blockArity_of_ok hm hbt, he₁, he₂]
    omega
  | @tryTable C bt cs body t₁ t₂ xs hbt hb hc =>
    have hs' : supported (liftInstrs body) = true := by simpa [liftInstr, supported1] using hsup
    obtain ⟨o, hcb, ho⟩ := IH hb (fun j hj => by
      have := List.sizeOf_lt_of_mem hj
      simp only [Instr.tryTable.sizeOf_spec] at hsz
      omega) hs' (ctxMatch_withLabel hm t₂) 0
    have he : endsAt (chkE (ehExt tags) F mi nl ret (t₂.length :: labels) (some t₁.length)
        (liftInstrs body)) t₂.length = true := by
      simp only [Nat.add_zero] at hcb ho
      rw [hcb]; rcases ho with rfl | rfl <;> simp [endsAt]
    obtain ⟨ns, hns, hok⟩ := catches_ok hm cs hc
    have hext : ehExt tags F mi (.tryTable bt cs []) = some (.catches ns) := by
      simp [ehExt, hns]
    refine good_single fun k => ⟨some (t₂.length + k), ?_, .inr rfl⟩
    simp [liftInstr, chk1E, hext, blockArity_of_ok hm hbt, he, hok]
    omega
  | br hl _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    simp [flatChkE, labels_get hm hl]
    omega
  | brIf hl =>
    refine good_op rfl fun k => ?_
    simp [flatChkE, labels_get hm hl]
  | @brTable C ls l' ts t₁ t₂ hls hl' _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    have hlab : ∀ l ∈ l' :: ls, ∃ lt, C.labels[l.toNat]? = some lt ∧ lt.length = ts.length := by
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · obtain ⟨lt, h₁, h₂⟩ := hl'
        exact ⟨lt, h₁, h₂.length_eq.symm⟩
      · obtain ⟨lt, h₁, h₂⟩ := hls l hl
        exact ⟨lt, h₁, h₂.length_eq.symm⟩
    have htab : tableOk labels (t₁.length + (ts.length + 1) + k - 1) (l' :: ls) = true := by
      simp only [tableOk, List.all_eq_true]
      intro l hl
      obtain ⟨lt, h₁, h₂⟩ := hlab l hl
      rw [labels_get hm h₁]
      simp only [h₂, decide_eq_true_eq]
      omega
    simp [flatChkE, htab]
  | brOnNull _ _ => have hx := xInstr_of_flat rfl hsup; simp [XProfile.xInstr] at hx
  | brOnNonNull _ => have hx := xInstr_of_flat rfl hsup; simp [XProfile.xInstr] at hx
  | brOnCast _ _ _ _ _ => have hx := xInstr_of_flat rfl hsup; simp [XProfile.xInstr] at hx
  | brOnCastFail _ _ _ _ _ => have hx := xInstr_of_flat rfl hsup; simp [XProfile.xInstr] at hx
  | call hf he =>
    refine good_op rfl fun k => ?_
    simp [flatChkE, flatEff, hm.funcs _ _ _ _ hf he]
    omega
  | callRef hd he =>
    refine good_op rfl fun k => ?_
    simp [flatChkE, ehExt, tExt, extStep, typeArity_of_ok hm hd he]
    omega
  | callIndirect _ _ hd he =>
    refine good_op rfl fun k => ?_
    simp [flatChkE, ehExt, tExt, extStep, typeArity_of_ok hm hd he]
    omega
  | return_ hr _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    simp [flatChkE, hm.ret _ hr]
    omega
  | returnCall hf he hr hrs _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    simp [flatChkE, ehExt, tExt, extStep, hm.funcs _ _ _ _ hf he, hm.ret _ hr, hrs.length_eq]
    omega
  | returnCallRef hd he hr hrs _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    simp [flatChkE, ehExt, tExt, extStep, typeArity_of_ok hm hd he, hm.ret _ hr, hrs.length_eq]
    omega
  | returnCallIndirect _ _ hd he hr hrs _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    simp [flatChkE, ehExt, tExt, extStep, typeArity_of_ok hm hd he, hm.ret _ hr, hrs.length_eq]
    omega
  | throw hx he _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    simp [flatChkE, ehExt, extStep, hm.tags _ _ _ hx he]
    omega
  | throwRef _ =>
    refine good_op rfl fun k => ⟨none, ?_, .inl rfl⟩
    simp [flatChkE, ehExt, extStep]

/-- `Good` for typed sequences of instructions below a size bound. -/
theorem good_lt : ∀ (n : Nat) {C : Context} {is : List Instr} {it : InstrType},
    InstrsOk C is it → (∀ i ∈ is, sizeOf i < n) → supported (liftInstrs is) = true →
      ∀ {nl ret : Nat} {labels : List Nat}, CtxMatch tags F mi nl ret labels C →
        Good (ehExt tags) F mi nl ret labels (liftInstrs is) it.params.length it.results.length
  | 0 => good_instrs (S := fun i => sizeOf i < 0) fun _ h _ _ => absurd h (Nat.not_lt_zero _)
  | n + 1 => good_instrs (S := fun i => sizeOf i < n + 1) fun hi hsz hsup hm =>
    good_instr (good_lt n) hi hsz hsup hm

end Complete

/-- **Relative completeness of the checker**: a typed, supported instruction sequence is
accepted from every height at least its parameter count, and never falls through or falls
through at its result count above the same frame. -/
theorem chkE_complete {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {C : Context} {is : List Instr}
    {t₁ t₂ : List Validation.CValType} {xs : List Nat}
    (hm : CtxMatch tags F mi nl ret labels C) (h : InstrsOk C is ⟨t₁, xs, t₂⟩)
    (hsup : supported (liftInstrs is) = true) (k : Nat) :
    ∃ o, chkE (ehExt tags) F mi nl ret labels (some (t₁.length + k)) (liftInstrs is) = some o ∧
      (o = none ∨ o = some (t₂.length + k)) :=
  good_lt (sizeOf is + 1) h (fun _ hi => by have := List.sizeOf_lt_of_mem hi; omega) hsup hm k

/-- **A valid, supported expression ends at its result count.** -/
theorem exprOk_endsAt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {C : Context} {e : List Instr}
    {ts : List Validation.CValType} (hm : CtxMatch tags F mi nl ret labels C)
    (h : ExprOk C e ts) (hsup : supported (liftInstrs e) = true) :
    endsAt (chkE (ehExt tags) F mi nl ret labels (some 0) (liftInstrs e)) ts.length = true := by
  obtain ⟨o, hc, ho⟩ := chkE_complete hm h hsup 0
  simp only [List.length_nil, Nat.add_zero] at hc ho
  rw [hc]
  rcases ho with rfl | rfl <;> simp [endsAt]

/-- **A typed store whose Wasm functions are supported is accepted by the exception checker**,
with its own tags. -/
theorem storeChkE_of_storeOk {s : Store H} (hs : StoreOk s) (hsup : StoreSupported s.funcs) :
    StoreChkE (ehExt s.tags) s.funcs := by
  intro a fi fn ps₀ rs₀ hfi hcode hty
  obtain ⟨C, ps, rs, lts, hb⟩ := Abstract.TypedCatValid.bodyOk_of_storeOk hs hfi hcode
  obtain ⟨hpl, hrl⟩ := Abstract.TypedCatValid.bodyOk_counts hs hfi hb hty
  have hll : fn.locals.length = lts.length := hb.locals.length_eq
  have hm := ctxMatch_funcBody (ps := ps.toList) (rs := rs.toList) (lts := lts)
    (nl := ps₀.length + fn.locals.length) hs hb.module (by rw [hpl, hll])
  rw [hrl] at hm
  have := exprOk_endsAt hm hb.body (hsup a fi fn hfi hcode)
  rwa [hrl] at this

theorem storeSupported_of_B {F : List (FuncInst H)} (h : storeSupportedB F = true) :
    StoreSupported F := by
  intro a fi fn hfi hcode
  have := List.all_eq_true.1 h fi (List.mem_of_getElem? hfi)
  simpa [funcSupported, hcode] using this

theorem storeSupportedB_of {F : List (FuncInst H)} (h : StoreSupported F) :
    storeSupportedB F = true := by
  refine List.all_eq_true.2 fun fi hfi => ?_
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hfi
  unfold funcSupported
  split
  · exact h a _ _ (List.getElem?_eq_some_iff.2 ⟨ha, rfl⟩) ‹_›
  · rfl

/-! ## The restriction is real -/

theorem floatBody_ok (C : Context) : ExprOk C floatBody [] := by
  have h₁ : InstrOk C (.floatConst .f32 0) ⟨[], [], [.num (.float .f32)]⟩ :=
    .numeric (.floatConst .f32 0)
  have h₂ : InstrOk (C.initLocals []) .drop ⟨[.num (.float .f32)], [], []⟩ :=
    .parametric (.drop (.num _))
  exact .cons h₁ (by simp) (.instr h₂)

theorem floatBody_unsupported : supported (liftInstrs floatBody) = false := rfl

theorem floatBody_rejected (ext : ExtArity H) (F : List (FuncInst H)) (mi : ModuleInst)
    (nl ret : Nat) (labels : List Nat) (h : Nat) :
    chkE ext F mi nl ret labels (some h) (liftInstrs floatBody) = none := rfl

end Silmaril.Proofs.Wasm.Interp.CheckComplete
