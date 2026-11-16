module

public import Silmaril.Proofs.Wasm.Interp.XProgress
public import Silmaril.Wasm.Execution.Core.Soundness.CallRefDef

/-!
# The operand of a typed reference call (proofs)

At a `call_ref y` (or `return_call_ref y`) site typed in context, in an instance with valid
types, the reference on top of the stack is null or a function reference of the store
(`callRef_top`). The context of the site need not be a whole frame's (`StateOk`): the instance's
valid types make its type context closed (`EmptyOk`), which is all the classification uses
(`hD_empty`, `refTo_classify`, as `CallRefDef.hD`/`callRef_inv_of` with `StateOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.CallRefDef Silmaril.Wasm.Validation.SubClosed

variable {H : Type}

/-- `CallRefDef.hD` for a closed type context. -/
theorem hD_empty {Δ : TypeCtx} (hE : Δ.EmptyOk) {d : DefType} {ps rs : Ty (.list .val)}
    (he : Expand d (.func ps rs)) :
    ∀ d₁ : DefType, TyOk {} d₁ →
      Relation.ReflTransGen (Sub Δ) (Ty.defHeap d₁) (Ty.defHeap d) →
      ∃ ps' rs', Expand d₁ (.func ps' rs') := by
  intro d₁ hd₁ hc
  set σ := σT Δ.types
  have h1 : Relation.ReflTransGen (Sub (trCtx Δ.types Δ)) ((Ty.defHeap d₁).subst σ)
      ((Ty.defHeap d).subst σ) :=
    hc.lift (fun t : CHeapType => t.subst σ) (fun _ _ hs => Sub.tr hE hs rfl)
  have e1 : (Ty.defHeap d₁).subst σ = Ty.defHeap d₁ := closed_σT (closed_of_empty (.use (.dt hd₁)))
  have e2 : (Ty.defHeap d).subst σ = Ty.defHeap (d.subst σ) := rfl
  rw [e1, e2] at h1
  obtain ⟨hg, hs⟩ := chain_heap_drop rfl h1 (hd₁ : Good (Ty.use (Ty.dt d₁)))
  have hd' : TyOk {} (d.subst σ) := hg
  have he' := expand_σT Δ.types he
  obtain ⟨ps', rs', he₁, -⟩ := Sub.defHeap_func_list hs hd₁ hd' he'
  exact ⟨ps', rs', he₁⟩

/-- **A reference typed below `ref null d`, `d` a function type, is null or a function.** -/
theorem refTo_classify {s : Store H} {Δ : TypeCtx} (hs : StoreOk s) (hE : Δ.EmptyOk)
    {d : DefType} {ps rs : Ty (.list .val)} (he : Expand d (.func ps rs)) {r : Ref}
    (hr : ValTo s Δ (.ref r) (Ty.refT true (Ty.defHeap d))) :
    r = .null ∨ ∃ (a : Nat) (fi : FuncInst H), r = .func a ∧ s.funcs[a]? = some fi := by
  have hD := hD_empty hE he
  obtain ⟨t₀, hv0, hc⟩ := hr
  cases hv0 with
  | @ref _ rt hro =>
  obtain ⟨rt₀, e, hrt, -⟩ := hro.principal
  have hc' : Relation.ReflTransGen (Sub Δ) (Ty.refv rt₀) (Ty.refT true (Ty.defHeap d)) := by
    rcases hrt with rfl | ⟨_, hsub⟩
    · exact hc
    · exact .head (.refv (Sub.of_empty hsub _)) hc
  cases r with
  | null => exact .inl rfl
  | i31 b =>
    cases e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | host a =>
    cases e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | extern r' =>
    cases e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | exn a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨_, _, rfl⟩ := e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | struct a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨si, h, rfl⟩ := e
    obtain ⟨ps', rs', he'⟩ := hD si.type (hs.struct_closed h) (rtg_heap_defHeap hc')
    obtain ⟨fs, hfs, -⟩ := hs.structs si (List.mem_of_getElem? h)
    exact absurd (Silmaril.Wasm.Execution.Core.Expand.func_eq he' hfs) (by intro h; cases h)
  | array a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ai, h, rfl⟩ := e
    obtain ⟨ps', rs', he'⟩ := hD ai.type (hs.array_closed h) (rtg_heap_defHeap hc')
    obtain ⟨ft, hft, -⟩ := hs.arrays ai (List.mem_of_getElem? h)
    exact absurd (Silmaril.Wasm.Execution.Core.Expand.func_eq he' hft) (by intro h; cases h)
  | func a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨fi, h, rfl⟩ := e
    exact .inr ⟨a, fi, rfl, h⟩

theorem forall₂_lastR {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β} {b : β}, List.Forall₂ R l (m ++ [b]) →
      ∃ l' a, l = l' ++ [a] ∧ List.Forall₂ R l' m ∧ R a b
  | _, [], _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _, _ :: _, _, .cons h hs => by
    obtain ⟨l', a, rfl, h', ha⟩ := forall₂_lastR hs
    exact ⟨_ :: l', a, rfl, .cons h h', ha⟩

/-- **The operand of a typed `call_ref y`**: the top of the stack is a null or a function
reference of the store. -/
theorem callRef_top {s : Store H} {f : Frame} {stk : List Val} {y : TypeIdx} {rest : List Admin}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain (.callRef y) :: rest⟩)
    (hm : Abstract.CallXT.TyTypes f.module) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧
      (r = .null ∨ ∃ (a : Nat) (fi : FuncInst H), r = .func a ∧ s.funcs[a]? = some fi) := by
  have typed : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.plain (.callRef y)]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using ht)
  obtain ⟨C, ts, xs, hs, hC, htypes, hcode⟩ := typed.fragment_types
  obtain ⟨mid, xs₁, _, hp, hi, _⟩ :=
    AdminsOk.split hcode hC (vals stk.reverse) [.plain (.callRef y)] rfl (by simp)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hi
  have hinstr := ha.plain_inv_ne
  obtain ⟨d, psT, rsT, hd, he, rfl⟩ : ∃ d psT rsT, (C.initLocals xs₁).type? y = some d ∧
      Expand d (.func psT rsT) ∧ it = .plain (psT.toList ++ [.refT true (.defHeap d)]) rsT.toList := by
    generalize C.initLocals xs₁ = C₀ at hinstr ⊢
    cases hinstr with
    | callRef hd he => exact ⟨_, _, _, hd, he, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h
  have hΔ : (C.initLocals xs₁).toTypeCtx = C.toTypeCtx := Context.initLocals_toTypeCtx C xs₁
  have hE : C.toTypeCtx.EmptyOk := fun d' hd' => by
    have : d' ∈ f.module.types := by
      rw [← htypes]; simpa [Context.toTypeCtx] using hd'
    obtain ⟨n, hn⟩ := List.getElem?_of_mem this
    have h' := hm n d' hn
    exact ⟨SubClosed.closed_of_empty h', h'⟩
  -- the top value, from the instruction's operand types down
  have h := hsub'.1
  simp only at h
  rw [← List.append_assoc] at h
  obtain ⟨l', tr, rfl, -, hr⟩ := forall₂_lastR h
  simp only [List.nil_append] at hsub
  obtain ⟨p', pr, rfl, -, hs₁⟩ := forall₂_lastR hsub
  obtain ⟨vs', v, hve, -, hvr⟩ := forall₂_lastR hv
  have hstk : stk = v :: vs'.reverse := by
    have := congrArg List.reverse hve
    simpa using this
  rw [hΔ] at hr
  have hto : ValTo s C.toTypeCtx v (Ty.refT true (Ty.defHeap d)) :=
    ⟨pr, hvr, (Relation.ReflTransGen.single hs₁).tail hr⟩
  obtain ⟨r, rfl⟩ := hto.ref
  exact ⟨r, vs'.reverse, hstk, refTo_classify hs hE he hto⟩

/-- **The operand of a typed `return_call_ref y`**: the top of the stack is a null or a function
reference of the store. -/
theorem returnCallRef_top {s : Store H} {f : Frame} {stk : List Val} {y : TypeIdx} {rest : List Admin}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain (.returnCallRef y) :: rest⟩)
    (hm : Abstract.CallXT.TyTypes f.module) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧
      (r = .null ∨ ∃ (a : Nat) (fi : FuncInst H), r = .func a ∧ s.funcs[a]? = some fi) := by
  have typed : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.plain (.returnCallRef y)]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using ht)
  obtain ⟨C, ts, xs, hs, hC, htypes, hcode⟩ := typed.fragment_types
  obtain ⟨mid, xs₁, _, hp, hi, _⟩ :=
    AdminsOk.split hcode hC (vals stk.reverse) [.plain (.returnCallRef y)] rfl (by simp)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hi
  have hinstr := ha.plain_inv_ne
  obtain ⟨d, psT, rsT, t₃, t₄, hd, he, rfl⟩ : ∃ (d : DefType) (psT rsT : Ty (.list .val))
      (t₃ t₄ : List CValType), (C.initLocals xs₁).type? y = some d ∧ Expand d (.func psT rsT) ∧
      it = .plain (t₃ ++ psT.toList ++ [.refT true (.defHeap d)]) t₄ := by
    generalize C.initLocals xs₁ = C₀ at hinstr ⊢
    cases hinstr with
    | returnCallRef hd he => exact ⟨_, _, _, _, _, hd, he, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h
  have hΔ : (C.initLocals xs₁).toTypeCtx = C.toTypeCtx := Context.initLocals_toTypeCtx C xs₁
  have hE : C.toTypeCtx.EmptyOk := fun d' hd' => by
    have : d' ∈ f.module.types := by
      rw [← htypes]; simpa [Context.toTypeCtx] using hd'
    obtain ⟨n, hn⟩ := List.getElem?_of_mem this
    have h' := hm n d' hn
    exact ⟨SubClosed.closed_of_empty h', h'⟩
  -- the top value, from the instruction's operand types down
  have h := hsub'.1
  simp only at h
  simp only [← List.append_assoc] at h
  obtain ⟨l', tr, rfl, -, hr⟩ := forall₂_lastR h
  simp only [List.nil_append] at hsub
  obtain ⟨p', pr, rfl, -, hs₁⟩ := forall₂_lastR hsub
  obtain ⟨vs', v, hve, -, hvr⟩ := forall₂_lastR hv
  have hstk : stk = v :: vs'.reverse := by
    have := congrArg List.reverse hve
    simpa using this
  rw [hΔ] at hr
  have hto : ValTo s C.toTypeCtx v (Ty.refT true (Ty.defHeap d)) :=
    ⟨pr, hvr, (Relation.ReflTransGen.single hs₁).tail hr⟩
  obtain ⟨r, rfl⟩ := hto.ref
  exact ⟨r, vs'.reverse, hstk, refTo_classify hs hE he hto⟩

end Silmaril.Wasm.Interp
