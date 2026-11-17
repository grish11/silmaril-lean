module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.StepGhost

@[expose] public section

/-!
# The supported profile is kept by Core steps (proofs)

`step_supp`: a host-free Core step of a supported configuration (`ASupp`, frames below the store's
tags) in a store whose Wasm functions are supported (`FuncsSupp`) reaches a supported
configuration, and keeps the tags and the functions. New code comes from the code, from function
bodies, from `call_indirect` (whose `ref.cast` is at a defined type) and from values.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {k : Nat}

/-- **Supported functions**: Wasm bodies are supported, modules name tags below the store's. -/
def FuncsSupp (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, FrameBelow s.tags.length ⟨[], fi.module⟩ ∧
    ∀ code, fi.code = .wasm code → ∀ i ∈ code.body, ISupp i

theorem isupp_atom_iff {i : Instr} (hs : ¬ Structured i) (hn : ¬ Unsupp i) : ISupp i ↔ True :=
  iff_true_intro (.atom hs hn)

theorem asupp_plain_iff {i : Instr} : ASupp k (.plain i) ↔ ISupp i :=
  ⟨fun h => by cases h; assumption, .plain⟩

theorem asupp_ref_iff {r : Ref} : ASupp k (.ref r) ↔ True := iff_true_intro (.ref r)

theorem asupp_trap_iff : ASupp k .trap ↔ True := iff_true_intro .trap

theorem asupp_toAdmin (v : Val) : ASupp k v.toAdmin := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · exact .plain (.atom (by simp [Structured]) (by simp [Unsupp]))
  · exact .plain (.atom (by simp [Structured]) (by simp [Unsupp]))
  · exact .plain (.atom (by simp [Structured]) (by simp [Unsupp]))
  · exact .ref r

theorem asupp_toAdmin_iff (v : Val) : ASupp k v.toAdmin ↔ True := iff_true_intro (asupp_toAdmin v)

theorem asupp_vals (vs : List Val) : ∀ a ∈ vals vs, ASupp k a := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
  exact asupp_toAdmin v

theorem asupp_expression {body : List Instr} (h : ∀ i ∈ body, ISupp i) :
    ∀ a ∈ expression body, ASupp k a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  exact .plain (h i hi)

theorem asupp_result (r : Result) : ∀ a ∈ r.toAdmin, ASupp k a := by
  intro a ha
  cases r with
  | values vs => exact asupp_vals vs a ha
  | throw t =>
    simp only [Result.toAdmin, List.mem_cons] at ha
    rcases ha with rfl | rfl | h
    · exact .ref _
    · exact .plain (.atom (by simp [Structured]) (by simp [Unsupp]))
    · simp at h
  | trap =>
    simp only [Result.toAdmin, List.mem_singleton] at ha
    subst ha; exact .trap

theorem forall_vals_iff (vs : List Val) : (∀ a ∈ vals vs, ASupp k a) ↔ True :=
  iff_true_intro (asupp_vals vs)

/-! ## Families -/

/-- Close the supported-code goals of a family step: values, references, traps and atomic
supported instructions. -/
macro "supp_close" : tactic => `(tactic| (
  simp [asupp_toAdmin_iff, asupp_plain_iff, asupp_ref_iff, asupp_trap_iff]
  all_goals (repeat' apply And.intro)
  all_goals (first | apply ASupp.plain | skip)
  all_goals (apply ISupp.atom <;> simp [Structured, Unsupp])))

section Families

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {c c' : Config H}

theorem VariableStep.supp (h : VariableStep c c') :
    (∀ a ∈ c'.code, ASupp k a) ∧ c'.store.tags = c.store.tags ∧ c'.store.funcs = c.store.funcs ∧
      c'.frame.module = c.frame.module := by
  cases h <;> refine ⟨?_, rfl, rfl, rfl⟩ <;> supp_close

theorem TableStep.supp (h : TableStep P c c') :
    (∀ a ∈ c'.code, ASupp k a) ∧ c'.store.tags = c.store.tags ∧ c'.store.funcs = c.store.funcs ∧
      c'.frame.module = c.frame.module := by
  cases h <;> refine ⟨?_, rfl, rfl, rfl⟩ <;> supp_close

theorem MemoryStep.supp (h : MemoryStep P c c') :
    (∀ a ∈ c'.code, ASupp k a) ∧ c'.store.tags = c.store.tags ∧ c'.store.funcs = c.store.funcs ∧
      c'.frame.module = c.frame.module := by
  cases h <;> refine ⟨?_, rfl, rfl, rfl⟩ <;> supp_close

theorem RefStep.supp (h : RefStep c c') :
    (∀ a ∈ c'.code, ASupp k a) ∧ c'.store.tags = c.store.tags ∧ c'.store.funcs = c.store.funcs ∧
      c'.frame.module = c.frame.module := by
  cases h <;> refine ⟨?_, rfl, rfl, rfl⟩ <;> supp_close

theorem ParametricStep.supp {is is' : List Admin} (h : ParametricStep is is') :
    ∀ a ∈ is', ASupp k a := by
  cases h <;> supp_close

theorem NumericStep.supp {is is' : List Admin} (h : NumericStep P is is') :
    ∀ a ∈ is', ASupp k a := by
  cases h <;> supp_close

theorem VectorStep.supp {is is' : List Admin} (h : VectorStep P is is') :
    ∀ a ∈ is', ASupp k a := by
  cases h <;> supp_close

end Families

/-! ## One step -/

theorem frameBelow_forCall {k : Nat} {m : ModuleInst} (h : FrameBelow k ⟨[], m⟩) (vs : List Val)
    (ls : List ValType) : FrameBelow k (Frame.forCall m vs ls) := h

theorem isupp_block_inv {bt : BlockType} {body : List Instr} (h : ISupp (.block bt body)) :
    ∀ i ∈ body, ISupp i := by
  cases h with
  | block _ h => exact h
  | atom hs _ => exact absurd trivial hs

theorem isupp_loop_inv {bt : BlockType} {body : List Instr} (h : ISupp (.loop bt body)) :
    ∀ i ∈ body, ISupp i := by
  cases h with
  | loop _ h => exact h
  | atom hs _ => exact absurd trivial hs

theorem isupp_if_inv {bt : BlockType} {b₁ b₂ : List Instr} (h : ISupp (.if_ bt b₁ b₂)) :
    (∀ i ∈ b₁, ISupp i) ∧ ∀ i ∈ b₂, ISupp i := by
  cases h with
  | if_ _ h₁ h₂ => exact ⟨h₁, h₂⟩
  | atom hs _ => exact absurd trivial hs

theorem isupp_try_inv {bt : BlockType} {cs : List Catch} {body : List Instr}
    (h : ISupp (.tryTable bt cs body)) : ∀ i ∈ body, ISupp i := by
  cases h with
  | tryTable _ _ h => exact h
  | atom hs _ => exact absurd trivial hs

theorem asupp_label_inv {n : Nat} {cont : List Instr} {body : List Admin}
    (h : ASupp k (.label n cont body)) : (∀ i ∈ cont, ISupp i) ∧ ∀ a ∈ body, ASupp k a := by
  cases h with
  | label _ hc hb => exact ⟨hc, hb⟩

theorem asupp_handler_inv {n : Nat} {cs : List Catch} {body : List Admin}
    (h : ASupp k (.handler n cs body)) : ∀ a ∈ body, ASupp k a := by
  cases h with
  | handler _ _ hb => exact hb

theorem asupp_frame_inv {n : Nat} {fr : Frame} {body : List Admin}
    (h : ASupp k (.frame n fr body)) : FrameBelow k fr ∧ ∀ a ∈ body, ASupp k a := by
  cases h with
  | frame _ hf hb => exact ⟨hf, hb⟩

theorem asupp_atom {i : Instr} (hs : ¬ Structured i) (hn : ¬ Unsupp i) : ASupp k (.plain i) :=
  .plain (.atom hs hn)

theorem asupp_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    ASupp k (c.retToCallIn m) := by
  rcases c with ⟨⟩ | _ | _ | d | _ | _ | _ | _ <;> try exact absurd hc id
  · rename_i i
    cases i <;> try exact absurd hc id
    simp only [Admin.retToCallIn]
    split
    · exact .callRefType _
    · exact asupp_atom (by simp [Structured]) (by simp [Unsupp])
  · exact .callRefType d

/-- **One host-free step keeps the supported profile**, the tags and the functions. -/
theorem step_supp {c c' : Config H} (h : Step P NH c c') (hF : FuncsSupp c.store)
    (hf : FrameBelow c.store.tags.length c.frame)
    (hs : ∀ a ∈ c.code, ASupp c.store.tags.length a) :
    c'.store.tags = c.store.tags ∧ c'.store.funcs = c.store.funcs ∧
      FrameBelow c.store.tags.length c'.frame ∧ ∀ a ∈ c'.code, ASupp c.store.tags.length a := by
  induction h with
  | parametric hp => exact ⟨rfl, rfl, hf, ParametricStep.supp hp⟩
  | numeric hp => exact ⟨rfl, rfl, hf, NumericStep.supp hp⟩
  | vector hp => exact ⟨rfl, rfl, hf, VectorStep.supp hp⟩
  | «variable» hp =>
    obtain ⟨h1, h2, h3, h4⟩ := VariableStep.supp (k := _) hp
    exact ⟨h2, h3, fun t ht => hf t (by rw [← h4]; exact ht), h1⟩
  | table hp =>
    obtain ⟨h1, h2, h3, h4⟩ := TableStep.supp (k := _) hp
    exact ⟨h2, h3, fun t ht => hf t (by rw [← h4]; exact ht), h1⟩
  | memory hp =>
    obtain ⟨h1, h2, h3, h4⟩ := MemoryStep.supp (k := _) hp
    exact ⟨h2, h3, fun t ht => hf t (by rw [← h4]; exact ht), h1⟩
  | reference hp =>
    obtain ⟨h1, h2, h3, h4⟩ := RefStep.supp (k := _) hp
    exact ⟨h2, h3, fun t ht => hf t (by rw [← h4]; exact ht), h1⟩
  | aggregate hp => exact (AggregateStep.not_supp hp hs).elim
  | ctxtInstrs hst hne ih =>
    simp only [List.forall_mem_append] at hs
    obtain ⟨h1, h2, h3, h4⟩ := ih hF hf hs.1.2
    refine ⟨h1, h2, h3, ?_⟩
    simp only [List.forall_mem_append]
    exact ⟨⟨asupp_vals _, h4⟩, hs.2⟩
  | ctxtLabel hst ih =>
    obtain ⟨hc, hb⟩ := asupp_label_inv (hs _ (List.mem_singleton_self _))
    obtain ⟨h1, h2, h3, h4⟩ := ih hF hf hb
    refine ⟨h1, h2, h3, ?_⟩
    rw [List.forall_mem_singleton]
    exact .label _ hc h4
  | ctxtHandler hst ih =>
    have hb := asupp_handler_inv (hs _ (List.mem_singleton_self _))
    obtain ⟨h1, h2, h3, h4⟩ := ih hF hf hb
    refine ⟨h1, h2, h3, ?_⟩
    rw [List.forall_mem_singleton]
    exact .handler _ _ h4
  | ctxtFrame hst ih =>
    obtain ⟨hfi, hb⟩ := asupp_frame_inv (hs _ (List.mem_singleton_self _))
    obtain ⟨h1, h2, h3, h4⟩ := ih hF hfi hb
    refine ⟨h1, h2, hf, ?_⟩
    rw [List.forall_mem_singleton]
    exact .frame _ h3 h4
  | block _ _ =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hs
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_singleton]
    refine .label _ (fun _ h => nomatch h) ?_
    rw [List.forall_mem_append]
    exact ⟨asupp_vals _, asupp_expression (isupp_block_inv (asupp_plain_iff.1 hs.2))⟩
  | loop _ _ =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hs
    have hl := asupp_plain_iff.1 hs.2
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_singleton]
    refine .label _ (fun i hi => by rw [List.mem_singleton.1 hi]; exact hl) ?_
    rw [List.forall_mem_append]
    exact ⟨asupp_vals _, asupp_expression (isupp_loop_inv hl)⟩
  | ifTrue _ =>
    simp only [List.forall_mem_cons] at hs
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_singleton]
    exact .plain (.block _ (isupp_if_inv (asupp_plain_iff.1 hs.2.1)).1)
  | ifFalse =>
    simp only [List.forall_mem_cons] at hs
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_singleton]
    exact .plain (.block _ (isupp_if_inv (asupp_plain_iff.1 hs.2.1)).2)
  | tryTable _ _ =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hs
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_singleton]
    refine .handler _ _ ?_
    rw [List.forall_mem_singleton]
    refine .label _ (fun _ h => nomatch h) ?_
    rw [List.forall_mem_append]
    exact ⟨asupp_vals _, asupp_expression (isupp_try_inv (asupp_plain_iff.1 hs.2))⟩
  | brLabelZero _ _ =>
    obtain ⟨hc, -⟩ := asupp_label_inv (hs _ (List.mem_singleton_self _))
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_append]
    exact ⟨asupp_vals _, asupp_expression hc⟩
  | callRefFunc _ hfi _ _ hcode =>
    obtain ⟨hb, hbody⟩ := hF _ (List.mem_of_getElem? hfi)
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_singleton]
    refine .frame _ (frameBelow_forCall hb _ _) ?_
    rw [List.forall_mem_singleton]
    exact .label _ (fun _ h => nomatch h) (asupp_expression (hbody _ hcode))
  | returnCallRefFrameAddr hc _ _ _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨asupp_vals _, .ref _, asupp_retToCallIn hc _, fun _ h => nomatch h⟩
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | throwRefHandlerCatch _ _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_singleton]
    exact ⟨asupp_vals _, asupp_atom (by simp [Structured]) (by simp [Unsupp])⟩
  | throwRefHandlerCatchRef _ _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨asupp_vals _, .ref _, asupp_atom (by simp [Structured]) (by simp [Unsupp]),
      fun _ h => nomatch h⟩
  | throwRefHandlerNext _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_singleton]
    exact .handler _ _ (asupp_handler_inv (hs _ (List.mem_singleton_self _)))
  | brLabelSucc _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    rw [List.forall_mem_append]
    exact ⟨asupp_vals _, by
      rw [List.forall_mem_singleton]; exact asupp_atom (by simp [Structured]) (by simp [Unsupp])⟩
  | brHandler =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_append.2 ⟨asupp_vals _, List.forall_mem_singleton.2
      (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | brIfTrue _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))
  | brIfFalse =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact fun _ h => nomatch h
  | brTableLt _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))
  | brTableGe _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))
  | brOnNullNull =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))
  | brOnNullAddr _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 (asupp_toAdmin _)
  | brOnNonNullNull =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact fun _ h => nomatch h
  | brOnNonNullAddr _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨asupp_toAdmin _, List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | brOnCastSucceed _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | brOnCastFail _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | brOnCastFailSucceed _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | brOnCastFailFail _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | call _ _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (.callRefType _)⟩
  | callRefNull _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 .trap
  | returnCall _ _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (.returnCallRefType _)⟩
  | returnCallRefLabel _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    have hb := (asupp_label_inv (hs _ (List.mem_singleton_self _))).2
    exact List.forall_mem_append.2 ⟨asupp_vals _, List.forall_mem_singleton.2 (hb _ (by simp))⟩
  | returnCallRefHandler _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    have hb := asupp_handler_inv (hs _ (List.mem_singleton_self _))
    exact List.forall_mem_append.2 ⟨asupp_vals _, List.forall_mem_singleton.2 (hb _ (by simp))⟩
  | returnCallRefFrameNull _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 .trap
  | callIndirect =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨asupp_atom (by simp [Structured]) (by simp [Unsupp]), List.forall_mem_cons.2 ⟨asupp_atom (by simp [Structured]) (by simp [Unsupp]),
      List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩⟩
  | returnCallIndirect =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨asupp_atom (by simp [Structured]) (by simp [Unsupp]), List.forall_mem_cons.2 ⟨asupp_atom (by simp [Structured]) (by simp [Unsupp]),
      List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩⟩
  | frameVals _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact asupp_vals _
  | returnFrame _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact asupp_vals _
  | returnLabel =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_append.2 ⟨asupp_vals _, List.forall_mem_singleton.2
      (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | returnHandler =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_append.2 ⟨asupp_vals _, List.forall_mem_singleton.2
      (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | labelVals =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact asupp_vals _
  | handlerVals =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact asupp_vals _
  | throw _ _ _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | throwRefNull =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 .trap
  | throwRefInstrs _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | throwRefLabel =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | throwRefFrame =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | throwRefHandlerEmpty =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | throwRefHandlerCatchAll =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))
  | throwRefHandlerCatchAllRef =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_cons.2 ⟨.ref _, List.forall_mem_singleton.2 (asupp_atom (by simp [Structured]) (by simp [Unsupp]))⟩
  | trapInstrs _ =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 .trap
  | trapLabel =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 .trap
  | trapHandler =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 .trap
  | trapFrame =>
    refine ⟨rfl, rfl, hf, ?_⟩
    exact List.forall_mem_singleton.2 .trap

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
