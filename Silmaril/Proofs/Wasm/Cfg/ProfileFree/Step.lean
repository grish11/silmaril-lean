module

public import Silmaril.Wasm.Cfg.ProfileFree.Defs
public import Silmaril.Wasm.Interp.CheckComplete.Defs
public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section

/-!
# Profile-free Core code: one step (proofs)

* `step_profile`: a Core step (any host) of profile-free code at the profile `P` is a step at
  every profile `P'`. Only the numeric, vector, memory and table rules mention the profile; the
  ones that read it (`PSens`) are excluded by `IFree`, and every other rule of these families is
  rebuilt with the same premises;
* `step_free`: a Core step keeps `ConfigFree` when the host keeps the functions profile-free
  (`HostFree`). New code comes from the code, from function bodies (`FuncsFree`), from values and
  from host results;
* `ifree_of_supported`, `funcsFree_of_storeSupported`: the checker's instruction profile
  (`XProfile.xInstr`, recursively) is profile-free.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ProfileFree

open Silmaril.Wasm.Cfg.ProfileFree Silmaril.Wasm.Cfg.DanglingTyped
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Binaryen (liftInstr liftInstrs)
open Silmaril.Wasm.Interp.CheckComplete (supported1 supported StoreSupported)

variable {H : Type}

/-! ## Basic facts -/

theorem ifree_atom_iff {i : Instr} (hs : ¬ Structured i) : IFree i ↔ ¬ PSens i :=
  ⟨fun h => by
    cases h with
    | atom _ hn => exact hn
    | _ => exact absurd trivial hs, fun hn => .atom hs hn⟩

theorem afree_plain_iff {i : Instr} : AFree (.plain i) ↔ IFree i :=
  ⟨fun h => by cases h; assumption, .plain⟩

theorem afree_ref_iff {r : Ref} : AFree (.ref r) ↔ True := iff_true_intro (.ref r)

theorem afree_trap_iff : AFree .trap ↔ True := iff_true_intro .trap

theorem afree_callRefType_iff {d : DefType} : AFree (.callRefType d) ↔ True :=
  iff_true_intro (.callRefType d)

theorem afree_returnCallRefType_iff {d : DefType} : AFree (.returnCallRefType d) ↔ True :=
  iff_true_intro (.returnCallRefType d)

theorem afree_atom {i : Instr} (hs : ¬ Structured i) (hn : ¬ PSens i) : AFree (.plain i) :=
  .plain (.atom hs hn)

theorem afree_toAdmin (v : Val) : AFree v.toAdmin := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · exact afree_atom (by simp [Structured]) (by simp [PSens])
  · exact afree_atom (by simp [Structured]) (by simp [PSens])
  · exact afree_atom (by simp [Structured]) (by simp [PSens])
  · exact .ref r

theorem afree_toAdmin_iff (v : Val) : AFree v.toAdmin ↔ True := iff_true_intro (afree_toAdmin v)

theorem afree_vals (vs : List Val) : ∀ a ∈ vals vs, AFree a := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
  exact afree_toAdmin v

theorem forall_vals_iff (vs : List Val) : (∀ a ∈ vals vs, AFree a) ↔ True :=
  iff_true_intro (afree_vals vs)

theorem forall_take_drop_ref_iff (n i : Nat) (l : List Ref) :
    (∀ a ∈ (l.map Admin.ref |>.drop i |>.take n), AFree a) ↔ True :=
  iff_true_intro fun a ha => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take ha))
    exact .ref r

theorem afree_expression {body : List Instr} (h : ∀ i ∈ body, IFree i) :
    ∀ a ∈ expression body, AFree a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  exact .plain (h i hi)

theorem afree_result (r : Result) : ∀ a ∈ r.toAdmin, AFree a := by
  intro a ha
  cases r with
  | values vs => exact afree_vals vs a ha
  | throw t =>
    simp only [Result.toAdmin, List.mem_cons] at ha
    rcases ha with rfl | rfl | h
    · exact .ref _
    · exact afree_atom (by simp [Structured]) (by simp [PSens])
    · simp at h
  | trap =>
    simp only [Result.toAdmin, List.mem_singleton] at ha
    subst ha; exact .trap

theorem ifree_block_inv {bt : BlockType} {body : List Instr} (h : IFree (.block bt body)) :
    ∀ i ∈ body, IFree i := by
  cases h with
  | block _ h => exact h
  | atom hs _ => exact absurd trivial hs

theorem ifree_loop_inv {bt : BlockType} {body : List Instr} (h : IFree (.loop bt body)) :
    ∀ i ∈ body, IFree i := by
  cases h with
  | loop _ h => exact h
  | atom hs _ => exact absurd trivial hs

theorem ifree_if_inv {bt : BlockType} {b₁ b₂ : List Instr} (h : IFree (.if_ bt b₁ b₂)) :
    (∀ i ∈ b₁, IFree i) ∧ ∀ i ∈ b₂, IFree i := by
  cases h with
  | if_ _ h₁ h₂ => exact ⟨h₁, h₂⟩
  | atom hs _ => exact absurd trivial hs

theorem ifree_try_inv {bt : BlockType} {cs : List Catch} {body : List Instr}
    (h : IFree (.tryTable bt cs body)) : ∀ i ∈ body, IFree i := by
  cases h with
  | tryTable _ _ h => exact h
  | atom hs _ => exact absurd trivial hs

theorem afree_label_inv {n : Nat} {cont : List Instr} {body : List Admin}
    (h : AFree (.label n cont body)) : (∀ i ∈ cont, IFree i) ∧ ∀ a ∈ body, AFree a := by
  cases h with
  | label _ hc hb => exact ⟨hc, hb⟩

theorem afree_handler_inv {n : Nat} {cs : List Catch} {body : List Admin}
    (h : AFree (.handler n cs body)) : ∀ a ∈ body, AFree a := by
  cases h with
  | handler _ _ hb => exact hb

theorem afree_frame_inv {n : Nat} {fr : Frame} {body : List Admin}
    (h : AFree (.frame n fr body)) : ∀ a ∈ body, AFree a := by
  cases h with
  | frame _ _ hb => exact hb

theorem afree_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    AFree (c.retToCallIn m) := by
  rcases c with ⟨⟩ | _ | _ | d | _ | _ | _ | _ <;> try exact absurd hc id
  · rename_i i
    cases i <;> try exact absurd hc id
    simp only [Admin.retToCallIn]
    split
    · exact .callRefType _
    · exact afree_atom (by simp [Structured]) (by simp [PSens])
  · exact .callRefType d

/-- A profile-sensitive last instruction contradicts profile-free code. -/
theorem psens_last {code : List Admin} {i : Instr} (hs : ∀ a ∈ code, AFree a)
    (hl : code.getLast? = some (.plain i)) (hp : PSens i) (hst : ¬ Structured i) : False :=
  (ifree_atom_iff hst).1 (afree_plain_iff.1 (hs _ (List.mem_of_getLast? hl))) hp

/-- Close the absurd case of a profile-sensitive rule. -/
macro "psens_absurd" hs:ident : tactic => `(tactic| (
  exfalso
  have h' := $hs _ (List.getLast_mem (by simp))
  simp only [aconst, List.getLast_cons, List.getLast_singleton, ne_eq, reduceCtorEq,
    not_false_eq_true, afree_plain_iff, List.getLast_append, List.cons_ne_nil] at h'
  exact (ifree_atom_iff (by simp [Structured])).1 h' trivial))

/-! ## Profile independence of one step -/

/-- **Profile transfer of one step**: on profile-free code, a Core step at profile `P` is a step
at every profile `P'` (same host). -/
theorem step_profile {P P' : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hs : ∀ a ∈ c.code, AFree a) : Step P' host c c' := by
  induction h with
  | parametric h => exact .parametric h
  | numeric h =>
    cases h with
    | intUnOp => exact .numeric .intUnOp
    | intBinOp hz => exact .numeric (.intBinOp hz)
    | intBinOpTrap he => exact .numeric (.intBinOpTrap he)
    | intTestOp => exact .numeric .intTestOp
    | intRelOp => exact .numeric .intRelOp
    | floatRelOp => exact .numeric .floatRelOp
    | floatUnOp => psens_absurd hs
    | floatBinOp => psens_absurd hs
    | convert => psens_absurd hs
    | convertTrap => psens_absurd hs
  | vector h => cases h <;> psens_absurd hs
  | «variable» h => exact .«variable» h
  | table h =>
    cases h with
    | growSucceed => psens_absurd hs
    | growFail => psens_absurd hs
    | _ => exact .table (by constructor! <;> assumption)
  | memory h =>
    cases h with
    | growSucceed => psens_absurd hs
    | growFail => psens_absurd hs
    | _ => exact .memory (by constructor! <;> assumption)
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih =>
    simp only [List.forall_mem_append] at hs
    exact .ctxtInstrs (ih hs.1.2) hne
  | ctxtLabel _ ih => exact .ctxtLabel (ih (afree_label_inv (hs _ (List.mem_singleton_self _))).2)
  | ctxtHandler _ ih => exact .ctxtHandler (ih (afree_handler_inv (hs _ (List.mem_singleton_self _))))
  | ctxtFrame _ ih => exact .ctxtFrame (ih (afree_frame_inv (hs _ (List.mem_singleton_self _))))
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact .callRefFunc hc hf he hn hcode
  | callRefHost hc hf he hn hcode hhost => exact .callRefHost hc hf he hn hcode hhost
  | callRefHostDiv hc hf he hn hcode hhost => exact .callRefHostDiv hc hf he hn hcode hhost
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc => exact .returnCallRefLabel hc
  | returnCallRefHandler hc => exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | throwRefInstrs hne => exact .throwRefInstrs hne
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .throwRefHandlerNext h
  | tryTable hbt hm => exact .tryTable hbt hm
  | handlerVals => exact .handlerVals
  | trapInstrs hne => exact .trapInstrs hne
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

/-! ## Preservation -/

/-- Close the profile-free goals of a family step: values, references, traps and atomic
profile-free instructions. -/
macro "free_close" : tactic => `(tactic| (
  try simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_singleton,
    forall_vals_iff, forall_take_drop_ref_iff, List.forall_mem_nil, and_true, true_and]
  try simp [afree_toAdmin_iff, afree_plain_iff, afree_ref_iff, afree_trap_iff,
    afree_callRefType_iff, afree_returnCallRefType_iff, forall_take_drop_ref_iff]
  all_goals (repeat' apply And.intro)
  all_goals (first | apply afree_atom <;> simp [Structured, PSens] | apply IFree.atom <;>
    simp [Structured, PSens] | skip)))

section Families

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Profile} {c c' : Config H}

theorem VariableStep.free (h : VariableStep c c') :
    (∀ a ∈ c'.code, AFree a) ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> refine ⟨?_, rfl⟩ <;> free_close

theorem TableStep.free (h : TableStep P c c') :
    (∀ a ∈ c'.code, AFree a) ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> refine ⟨?_, rfl⟩ <;> free_close

theorem MemoryStep.free (h : MemoryStep P c c') :
    (∀ a ∈ c'.code, AFree a) ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> refine ⟨?_, rfl⟩ <;> free_close

theorem RefStep.free (h : RefStep c c') :
    (∀ a ∈ c'.code, AFree a) ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> refine ⟨?_, rfl⟩ <;> free_close

theorem AggregateStep.free (h : AggregateStep c c') :
    (∀ a ∈ c'.code, AFree a) ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> refine ⟨?_, rfl⟩ <;> free_close

theorem ParametricStep.free {is is' : List Admin} (h : ParametricStep is is') :
    ∀ a ∈ is', AFree a := by
  cases h <;> free_close

theorem NumericStep.free {is is' : List Admin} (h : NumericStep P is is') :
    ∀ a ∈ is', AFree a := by
  cases h <;> free_close

theorem VectorStep.free {is is' : List Admin} (h : VectorStep P is is') :
    ∀ a ∈ is', AFree a := by
  cases h <;> free_close

end Families

/-- **One step keeps profile-free code and profile-free functions** (every profile), when host
answers keep the functions profile-free. -/
theorem step_free {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hH : HostFree host) (hF : FuncsFree c.store.funcs)
    (hs : ∀ a ∈ c.code, AFree a) : FuncsFree c'.store.funcs ∧ ∀ a ∈ c'.code, AFree a := by
  induction h with
  | parametric hp => exact ⟨hF, ParametricStep.free hp⟩
  | numeric hp => exact ⟨hF, NumericStep.free hp⟩
  | vector hp => exact ⟨hF, VectorStep.free hp⟩
  | «variable» hp => exact ⟨(VariableStep.free hp).2 ▸ hF, (VariableStep.free hp).1⟩
  | table hp => exact ⟨(TableStep.free hp).2 ▸ hF, (TableStep.free hp).1⟩
  | memory hp => exact ⟨(MemoryStep.free hp).2 ▸ hF, (MemoryStep.free hp).1⟩
  | reference hp => exact ⟨(RefStep.free hp).2 ▸ hF, (RefStep.free hp).1⟩
  | aggregate hp => exact ⟨(AggregateStep.free hp).2 ▸ hF, (AggregateStep.free hp).1⟩
  | ctxtInstrs hst hne ih =>
    simp only [List.forall_mem_append] at hs
    obtain ⟨h1, h2⟩ := ih hF hs.1.2
    refine ⟨h1, ?_⟩
    simp only [List.forall_mem_append]
    exact ⟨⟨afree_vals _, h2⟩, hs.2⟩
  | ctxtLabel hst ih =>
    obtain ⟨hc, hb⟩ := afree_label_inv (hs _ (List.mem_singleton_self _))
    obtain ⟨h1, h2⟩ := ih hF hb
    exact ⟨h1, List.forall_mem_singleton.2 (.label _ hc h2)⟩
  | ctxtHandler hst ih =>
    obtain ⟨h1, h2⟩ := ih hF (afree_handler_inv (hs _ (List.mem_singleton_self _)))
    exact ⟨h1, List.forall_mem_singleton.2 (.handler _ _ h2)⟩
  | ctxtFrame hst ih =>
    obtain ⟨h1, h2⟩ := ih hF (afree_frame_inv (hs _ (List.mem_singleton_self _)))
    exact ⟨h1, List.forall_mem_singleton.2 (.frame _ _ h2)⟩
  | block _ _ =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hs
    refine ⟨hF, List.forall_mem_singleton.2 (.label _ (fun _ h => nomatch h) ?_)⟩
    rw [List.forall_mem_append]
    exact ⟨afree_vals _, afree_expression (ifree_block_inv (afree_plain_iff.1 hs.2))⟩
  | loop _ _ =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hs
    have hl := afree_plain_iff.1 hs.2
    refine ⟨hF, List.forall_mem_singleton.2
      (.label _ (fun i hi => by rw [List.mem_singleton.1 hi]; exact hl) ?_)⟩
    rw [List.forall_mem_append]
    exact ⟨afree_vals _, afree_expression (ifree_loop_inv hl)⟩
  | ifTrue _ =>
    simp only [List.forall_mem_cons] at hs
    exact ⟨hF, List.forall_mem_singleton.2
      (.plain (.block _ (ifree_if_inv (afree_plain_iff.1 hs.2.1)).1))⟩
  | ifFalse =>
    simp only [List.forall_mem_cons] at hs
    exact ⟨hF, List.forall_mem_singleton.2
      (.plain (.block _ (ifree_if_inv (afree_plain_iff.1 hs.2.1)).2))⟩
  | tryTable _ _ =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hs
    refine ⟨hF, List.forall_mem_singleton.2 (.handler _ _ (List.forall_mem_singleton.2
      (.label _ (fun _ h => nomatch h) ?_)))⟩
    rw [List.forall_mem_append]
    exact ⟨afree_vals _, afree_expression (ifree_try_inv (afree_plain_iff.1 hs.2))⟩
  | brLabelZero _ _ =>
    obtain ⟨hc, -⟩ := afree_label_inv (hs _ (List.mem_singleton_self _))
    exact ⟨hF, List.forall_mem_append.2 ⟨afree_vals _, afree_expression hc⟩⟩
  | callRefFunc _ hfi _ _ hcode =>
    exact ⟨hF, List.forall_mem_singleton.2 (.frame _ _ (List.forall_mem_singleton.2
      (.label _ (fun _ h => nomatch h)
        (afree_expression (hF _ (List.mem_of_getElem? hfi) _ hcode)))))⟩
  | returnCallRefFrameAddr hc _ _ _ =>
    refine ⟨hF, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_cons]
    exact ⟨afree_vals _, .ref _, afree_retToCallIn hc _, fun _ h => nomatch h⟩
  | callRefHost _ _ _ _ _ hhost => exact ⟨hH _ _ _ _ _ hhost hF, afree_result _⟩
  | callRefHostDiv _ _ _ _ _ _ => exact ⟨hF, hs⟩
  | throwRefHandlerNext _ =>
    exact ⟨hF, List.forall_mem_singleton.2
      (.handler _ _ (afree_handler_inv (hs _ (List.mem_singleton_self _))))⟩
  | returnCallRefLabel _ =>
    have hb := (afree_label_inv (hs _ (List.mem_singleton_self _))).2
    exact ⟨hF, List.forall_mem_append.2
      ⟨afree_vals _, List.forall_mem_singleton.2 (hb _ (by simp))⟩⟩
  | returnCallRefHandler _ =>
    have hb := afree_handler_inv (hs _ (List.mem_singleton_self _))
    exact ⟨hF, List.forall_mem_append.2
      ⟨afree_vals _, List.forall_mem_singleton.2 (hb _ (by simp))⟩⟩
  | _ => exact ⟨hF, by free_close⟩

/-! ## The checker's profile is profile-free -/

theorem liftInstr_atom {i : Instr} (hs : ¬ Structured i) : liftInstr i = .op i [] := by
  cases i <;> simp_all [Structured, liftInstr]

theorem not_psens_of_xInstr {i : Instr} (h : Interp.XProfile.xInstr i = true) : ¬ PSens i := by
  cases i <;> simp_all [Interp.XProfile.xInstr, PSens]

mutual
/-- **An instruction in the checker's profile is profile-free.** -/
theorem ifree_of_supported (i : Instr) (h : supported1 (liftInstr i) = true) : IFree i := by
  by_cases hs : Structured i
  · match i, h, hs with
    | .block bt body, h, _ =>
      exact .block bt (ifrees_of_supported body (by simpa [liftInstr, supported1] using h))
    | .loop bt body, h, _ =>
      exact .loop bt (ifrees_of_supported body (by simpa [liftInstr, supported1] using h))
    | .if_ bt t e, h, _ =>
      simp only [liftInstr, supported1, Bool.and_eq_true] at h
      exact .if_ bt (ifrees_of_supported t h.1.2) (ifrees_of_supported e h.2)
    | .tryTable bt cs body, h, _ =>
      exact .tryTable bt cs (ifrees_of_supported body (by simpa [liftInstr, supported1] using h))
    | .unreachable, _, hs | .nop, _, hs => simp [Structured] at hs
  · rw [liftInstr_atom hs] at h
    simp only [supported1, Bool.and_eq_true] at h
    exact .atom hs (not_psens_of_xInstr h.1)
termination_by sizeOf i
decreasing_by all_goals (simp_wf; first | done | omega)

/-- **A sequence in the checker's profile is profile-free.** -/
theorem ifrees_of_supported (is : List Instr) (h : supported (liftInstrs is) = true) :
    ∀ i ∈ is, IFree i := by
  match is, h with
  | [], _ => exact fun _ h => nomatch h
  | j :: js, h =>
    simp only [liftInstrs, supported, Bool.and_eq_true] at h
    intro i hi
    cases hi with
    | head => exact ifree_of_supported j h.1
    | tail _ hi => exact ifrees_of_supported js h.2 i hi
termination_by sizeOf is
decreasing_by all_goals (simp_wf; first | done | omega)
end

/-- **Functions in the checker's profile are profile-free.** -/
theorem funcsFree_of_storeSupported {F : List (FuncInst H)} (hsup : StoreSupported F) :
    FuncsFree F := by
  intro fi hfi code hcode
  obtain ⟨a, ha, hfa⟩ := List.getElem_of_mem hfi
  have hget : F[a]? = some fi := by rw [List.getElem?_eq_getElem ha, hfa]
  exact ifrees_of_supported _ (hsup a fi code hget hcode)

end Silmaril.Wasm.Cfg.Proofs.ProfileFree
