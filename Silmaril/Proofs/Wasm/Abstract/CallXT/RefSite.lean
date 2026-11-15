module

public import Silmaril.Proofs.Wasm.Abstract.CallXT.Cast
public import Silmaril.Wasm.Execution.Core.Sim.TypedBlock
public import Silmaril.Wasm.Execution.Core.Soundness.RefTyping

/-!
Proofs for `Silmaril.Wasm.Abstract.CallXT.Thms`: **the `call_ref` premise at a
typed site.** If the Core configuration at a `call_ref y` on a function
reference is typed in context (`Sim.ContextTyped`), in an instance with valid
types, then the referenced function has the counts of `y`
(`typeArity_of_callRef_site`).

The site's typing splits into the values and the instruction (`AdminsOk.split`,
`AdminsOk.vals_inv`, `AdminsOk.single_inv`); the reference's value type is below
`call_ref`'s operand `ref null y`; its own typing chain starts at its function's
type (`refOk_func_sub`); the whole chain projects to heap types
(`rtg_heap_defHeap`), and counts survive it (`counts_of_ctx_chain`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CallXT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Abstract.CallXT

variable {H : Type}

theorem forall₂_last {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β} {b : β}, List.Forall₂ R l (m ++ [b]) →
      ∃ l' a, l = l' ++ [a] ∧ List.Forall₂ R l' m ∧ R a b
  | _, [], _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _, _ :: _, _, .cons h hs => by
    obtain ⟨l', a, rfl, h', ha⟩ := forall₂_last hs
    exact ⟨_ :: l', a, rfl, .cons h h', ha⟩

theorem forall₂_last_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {a : α} {m : List β}, List.Forall₂ R (l ++ [a]) m →
      ∃ m' b, m = m' ++ [b] ∧ List.Forall₂ R l m' ∧ R a b
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h hs => by
    obtain ⟨m', b, rfl, h', hb⟩ := forall₂_last_left hs
    exact ⟨_ :: m', b, rfl, .cons h h', hb⟩

/-- **The `call_ref` premise at a typed site.** -/
theorem typeArity_of_callRef_site {s : Store H} {f : Frame} {stk : List Val} {fa : Nat}
    {y : TypeIdx} {rest : List Admin} {fi : FuncInst H} {ps rs : List CValType}
    (ht : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++
      .plain (.callRef y) :: rest⟩)
    (hm : TyTypes f.module) (hfi : s.funcs[fa]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) :
    typeArity f.module y = some (ps.length, rs.length) := by
  have typed : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++
      [.plain (.callRef y)]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using ht)
  obtain ⟨C, ts, xs, _, hC, htypes, hcode⟩ := typed.fragment_types
  obtain ⟨mid, xs₁, _, hp, hi, _⟩ :=
    AdminsOk.split hcode hC (vals (.ref (.func fa) :: stk).reverse) [.plain (.callRef y)] rfl
      (by simp)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hi
  have hinstr := ha.plain_inv_ne
  -- the instruction's operand type
  obtain ⟨d, psT, rsT, hd, he, rfl⟩ : ∃ d psT rsT, (C.initLocals xs₁).type? y = some d ∧
      Expand d (.func psT rsT) ∧ it = .plain (psT.toList ++ [.refT true (.defHeap d)]) rsT.toList := by
    generalize C.initLocals xs₁ = C₀ at hinstr ⊢
    cases hinstr with
    | callRef hd he => exact ⟨_, _, _, hd, he, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h
  have hdm : f.module.types[y.toNat]? = some d := by
    have : (C.initLocals xs₁).types = C.types := by
      exact congrArg TypeCtx.types (Context.initLocals_toTypeCtx C xs₁)
    simpa [Context.type?, this, htypes] using hd
  have hdok : TyOk {} d := hm _ _ hdm
  -- the reference's value type, below the operand
  simp only [List.reverse_cons] at hv
  obtain ⟨pushed', pr, rfl, -, hvr⟩ := forall₂_last_left hv
  simp only [List.nil_append] at hsub
  obtain ⟨mid', tr, rfl, -, hs₁⟩ := forall₂_last_left hsub
  have hs₂ : Sub (C.initLocals xs₁).toTypeCtx tr (.refT true (.defHeap d)) := by
    have h := hsub'.1
    simp only at h
    rw [← List.append_assoc] at h
    obtain ⟨l', a, hla, -, hr⟩ := forall₂_last h
    have hat : [tr] = [a] := (List.append_inj' hla rfl).2
    simp only [List.cons.injEq, and_true] at hat
    exact hat ▸ hr
  have hΔ : (C.initLocals xs₁).toTypeCtx = C.toTypeCtx := Context.initLocals_toTypeCtx C xs₁
  rw [hΔ] at hs₂
  -- the reference's own typing chain
  cases hvr with
  | @ref r rt₀ hro =>
    obtain ⟨fi', hfi', hc⟩ := refOk_func_sub hro
    rw [hfi] at hfi'; cases hfi'
    have hbase : Relation.ReflTransGen (Sub C.toTypeCtx)
        (Ty.refv (.ref false (.use (.dt fi.type)))) (Ty.refv rt₀) := by
      rcases hc with rfl | ⟨-, hs⟩
      · exact .refl
      · exact .single (.refv (Sub.of_empty hs _))
    have hchain : Relation.ReflTransGen (Sub C.toTypeCtx)
        (Ty.refv (.ref false (.use (.dt fi.type)))) (Ty.refT true (Ty.defHeap d)) :=
      (hbase.tail hs₁).tail hs₂
    have hheap := Silmaril.Wasm.Execution.Core.rtg_heap_defHeap hchain
    have hE : C.toTypeCtx.EmptyOk := fun d' hd' => by
      have : d' ∈ f.module.types := by
        rw [← htypes]; simpa [Context.toTypeCtx] using hd'
      obtain ⟨n, hn⟩ := List.getElem?_of_mem this
      have h' := hm n d' hn
      exact ⟨SubClosed.closed_of_empty h', h'⟩
    obtain ⟨ps₂, rs₂, h₂, hp₂, hr₂⟩ := counts_of_ctx_chain hE hfiok hdok hheap hty
    simp [typeArity, hdm, h₂, hp₂, hr₂]

/-- **The `return_call_ref` premise at a typed site.** -/
theorem typeArity_of_returnCallRef_site {s : Store H} {f : Frame} {stk : List Val} {fa : Nat}
    {y : TypeIdx} {rest : List Admin} {fi : FuncInst H} {ps rs : List CValType}
    (ht : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++
      .plain (.returnCallRef y) :: rest⟩)
    (hm : TyTypes f.module) (hfi : s.funcs[fa]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) :
    typeArity f.module y = some (ps.length, rs.length) := by
  have typed : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++
      [.plain (.returnCallRef y)]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using ht)
  obtain ⟨C, ts, xs, _, hC, htypes, hcode⟩ := typed.fragment_types
  obtain ⟨mid, xs₁, _, hp, hi, _⟩ :=
    AdminsOk.split hcode hC (vals (.ref (.func fa) :: stk).reverse) [.plain (.returnCallRef y)] rfl
      (by simp)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hi
  have hinstr := ha.plain_inv_ne
  -- the instruction's operand type
  obtain ⟨d, psT, t₃, t₄, hd, rfl⟩ : ∃ (d : DefType) (psT : Ty (.list .val)) (t₃ t₄ : List CValType),
      (C.initLocals xs₁).type? y = some d ∧
      it = .plain (t₃ ++ psT.toList ++ [.refT true (.defHeap d)]) t₄ := by
    generalize C.initLocals xs₁ = C₀ at hinstr ⊢
    cases hinstr with
    | returnCallRef hd he => exact ⟨_, _, _, _, hd, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h
  have hdm : f.module.types[y.toNat]? = some d := by
    have : (C.initLocals xs₁).types = C.types := by
      exact congrArg TypeCtx.types (Context.initLocals_toTypeCtx C xs₁)
    simpa [Context.type?, this, htypes] using hd
  have hdok : TyOk {} d := hm _ _ hdm
  -- the reference's value type, below the operand
  simp only [List.reverse_cons] at hv
  obtain ⟨pushed', pr, rfl, -, hvr⟩ := forall₂_last_left hv
  simp only [List.nil_append] at hsub
  obtain ⟨mid', tr, rfl, -, hs₁⟩ := forall₂_last_left hsub
  have hs₂ : Sub (C.initLocals xs₁).toTypeCtx tr (.refT true (.defHeap d)) := by
    have h := hsub'.1
    simp only at h
    simp only [← List.append_assoc] at h
    obtain ⟨l', a, hla, -, hr⟩ := forall₂_last h
    have hat : [tr] = [a] := (List.append_inj' hla rfl).2
    simp only [List.cons.injEq, and_true] at hat
    exact hat ▸ hr
  have hΔ : (C.initLocals xs₁).toTypeCtx = C.toTypeCtx := Context.initLocals_toTypeCtx C xs₁
  rw [hΔ] at hs₂
  -- the reference's own typing chain
  cases hvr with
  | @ref r rt₀ hro =>
    obtain ⟨fi', hfi', hc⟩ := refOk_func_sub hro
    rw [hfi] at hfi'; cases hfi'
    have hbase : Relation.ReflTransGen (Sub C.toTypeCtx)
        (Ty.refv (.ref false (.use (.dt fi.type)))) (Ty.refv rt₀) := by
      rcases hc with rfl | ⟨-, hs⟩
      · exact .refl
      · exact .single (.refv (Sub.of_empty hs _))
    have hchain : Relation.ReflTransGen (Sub C.toTypeCtx)
        (Ty.refv (.ref false (.use (.dt fi.type)))) (Ty.refT true (Ty.defHeap d)) :=
      (hbase.tail hs₁).tail hs₂
    have hheap := Silmaril.Wasm.Execution.Core.rtg_heap_defHeap hchain
    have hE : C.toTypeCtx.EmptyOk := fun d' hd' => by
      have : d' ∈ f.module.types := by
        rw [← htypes]; simpa [Context.toTypeCtx] using hd'
      obtain ⟨n, hn⟩ := List.getElem?_of_mem this
      have h' := hm n d' hn
      exact ⟨SubClosed.closed_of_empty h', h'⟩
    obtain ⟨ps₂, rs₂, h₂, hp₂, hr₂⟩ := counts_of_ctx_chain hE hfiok hdok hheap hty
    simp [typeArity, hdm, h₂, hp₂, hr₂]

end Silmaril.Proofs.Wasm.Abstract.CallXT
