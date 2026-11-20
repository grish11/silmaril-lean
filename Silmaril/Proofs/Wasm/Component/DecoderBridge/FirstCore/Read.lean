module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Wire
public import Silmaril.Wasm.Component.DecoderBridge.FirstCore.Defs

/-!
# The first node of the symbolic reading

`refRead_first`: the first node of the symbolic reading `refRead r` (`DecoderBridge.Wire`) is
the module of the first core instantiation of `r`, the module at its index among the core
modules defined before it (`firstCore?`, `coreMods`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Proofs.Wasm.Component.DecoderBridge (RDef)

theorem refStep_prefix {R R' : RSt} {d : RDef} (h : refStep R d = some R') :
    R.nodes <+: R'.nodes := by
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; exact List.prefix_refl _)
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h; aesop)

theorem refStep_other {R R' : RSt} {d : RDef}
    (hd : ∀ mi args, d ≠ .coreInstance (.instantiate mi args)) (h : refStep R d = some R') :
    R'.nodes = R.nodes ∧ R'.mods = R.mods ++ coreMods [d] := by
  unfold refStep at h
  split at h
  · cases h; simp [coreMods]
  all_goals first
    | exact absurd rfl (hd _ _)
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h; aesop (add norm coreMods))

theorem refStep_inst {R R' : RSt} {mi : Nat} {args : List (String × Nat)}
    (h : refStep R (.coreInstance (.instantiate mi args)) = some R') :
    ∃ m w, R.mods[mi]? = some m ∧ R'.nodes = R.nodes ++ [(m, w)] := by
  simp only [refStep, bind, Option.bind_eq_some_iff] at h
  obtain ⟨m, hm, ⟨names, _, exps⟩, -, w, -, h⟩ := h
  injection h with h
  subst h
  exact ⟨m, w, hm, rfl⟩

theorem foldlM_prefix : ∀ {ds : List RDef} {R R' : RSt}, ds.foldlM refStep R = some R' →
    R.nodes <+: R'.nodes
  | [], R, R', h => by simp at h; subst h; exact List.prefix_refl _
  | d :: ds, R, R', h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      exact (refStep_prefix hR).trans (foldlM_prefix h)

theorem preOk_noInst : ∀ {nf ncf : Nat} {ds : List RDef}, preOk nf ncf ds = true →
    ∀ d ∈ ds, ∀ mi args, d ≠ .coreInstance (.instantiate mi args)
  | _, _, [], _, d, hd => by simp at hd
  | nf, ncf, d :: ds, h, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro mi args hd
      subst hd
      simp [preOk] at h
    · match d, h with
      | .coreModule _, h => simp only [preOk] at h; exact preOk_noInst h e he'
      | .type (.func _), h =>
        simp only [preOk, Bool.and_eq_true] at h; exact preOk_noInst h.2 e he'
      | .import_ _ (.func _), h => simp only [preOk] at h; exact preOk_noInst h e he'
      | .canon (.lower _ []), h =>
        simp only [preOk, Bool.and_eq_true] at h; exact preOk_noInst h.2 e he'
      | .coreInstance (.exports _), h =>
        simp only [preOk, Bool.and_eq_true] at h; exact preOk_noInst h.2 e he'

theorem foldlM_other : ∀ {ds : List RDef} {R R' : RSt},
    (∀ d ∈ ds, ∀ mi args, d ≠ .coreInstance (.instantiate mi args)) →
    ds.foldlM refStep R = some R' → R'.nodes = R.nodes ∧ R'.mods = R.mods ++ coreMods ds
  | [], R, R', _, h => by simp at h; subst h; simp [coreMods]
  | d :: ds, R, R', hd, h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      obtain ⟨a1, b1⟩ := refStep_other (hd d (by simp)) hR
      obtain ⟨a2, b2⟩ := foldlM_other (fun e he => hd e (by simp [he])) h
      refine ⟨a2.trans a1, ?_⟩
      rw [b2, b1, List.append_assoc]
      congr 1
      cases d <;> simp [coreMods]

/-- **The first node of the symbolic reading** is the module of the first core instantiation. -/
theorem refRead_first {r : Conformance.RefComponent} {R : RSt} {pre post : List RDef} {mi : Nat}
    {cargs : List (String × Nat)} (hs : r = pre ++ .coreInstance (.instantiate mi cargs) :: post)
    (hp : preOk 0 0 pre = true) (hR : refRead r = some R) :
    ∃ m w, (coreMods pre)[mi]? = some m ∧ R.nodes[0]? = some (m, w) := by
  unfold refRead at hR
  rw [hs, List.foldlM_append] at hR
  simp only [bind, Option.bind_eq_some_iff, List.foldlM_cons] at hR
  obtain ⟨R₁, h₁, R₂, h₂, hR⟩ := hR
  obtain ⟨hn₁, hm₁⟩ := foldlM_other (preOk_noInst hp) h₁
  obtain ⟨m, w, hm, hn₂⟩ := refStep_inst h₂
  have hpre := foldlM_prefix hR
  rw [hm₁] at hm
  simp only [List.nil_append] at hm
  refine ⟨m, w, hm, ?_⟩
  rw [hn₂, hn₁] at hpre
  obtain ⟨t, ht⟩ := hpre
  rw [← ht]
  simp

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
