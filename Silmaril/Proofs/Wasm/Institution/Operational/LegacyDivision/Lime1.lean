module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Lime1.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision.Lime1.Proofs

open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Runtime

private def supported : Admin → Bool
  | .source (.intConst ..) | .source (.floatConst ..) | .source (.intBinOp _ (.div _))
  | .source .nop | .trap => true
  | _ => false

private theorem test {a : Admin} (h : Allowed scalarSyntax a) : supported a = true := by
  cases h with
  | value v => rcases v with ⟨t, bits⟩; cases t <;> rfl
  | _ => rfl

private theorem tests {xs : List Admin} (h : Supported xs) : ∀ a ∈ xs, supported a = true :=
  fun a ha => test (h a ha)

private theorem split {xs ys : List Admin} (h : Supported (xs ++ ys)) :
    Supported xs ∧ Supported ys := admitted_append.mp h

theorem pure_sound {types : List Silmaril.Wasm.Lime1.FuncType} {xs ys : List Admin} (h : Redex scalarSyntax xs ys) : PureStep types xs ys := by
  cases h with
  | divide t sign x y z ok => exact .intBinary t (.div sign) x y z ok
  | divTrap t sign x y cause trap => exact .intBinaryTrap t (.div sign) x y cause trap
  | nop => exact .nop
  | trapValues v vs tail _ => exact .trapValues v vs tail
  | trapTail a tail _ => exact .trapTail a tail

theorem pure_readback {types : List Silmaril.Wasm.Lime1.FuncType} {xs ys : List Admin} (h : PureStep types xs ys) (ready : Supported xs) :
    Redex scalarSyntax xs ys := by
  have checked := tests ready
  cases h with
  | nop => exact .nop
  | intBinary t op x y z ok =>
    cases op <;> simp [supported] at checked
    exact .divide t _ x y z ok
  | intBinaryTrap t op x y cause trap =>
    cases op <;> simp [supported] at checked
    exact .divTrap t _ x y cause trap
  | trapValues v vs tail =>
    exact .trapValues v vs tail (split ready).2
  | trapTail a tail =>
    exact .trapTail a tail (admitted_cons.mp ready).2
  | _ =>
    simp only [List.forall_mem_append, List.forall_mem_cons, supported, Bool.false_eq_true, and_false, false_and] at checked

theorem step_sound {H : Type} {host : HostSemantics H} (s : Store H) (f : Frame)
    {xs ys : List Admin} (h : Derives xs ys) : Step host ⟨s, f, xs⟩ ⟨s, f, ys⟩ :=
  Silmaril.Semantics.SOS.Derives.least
    (M := fun j => Step host ⟨s, f, j.1⟩ ⟨s, f, j.2⟩) h (by
      intro r hr ih
      change RuleInstance scalarSyntax r at hr
      cases hr with
      | redex redex => exact .pure s f (pure_sound redex)
      | context saved before after tail _ => exact .context (ih (before, after) (List.Mem.head _)) saved tail)

theorem step_readback {H : Type} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) (ready : Supported a.code) :
    Derives a.code b.code ∧ a.store = b.store ∧ a.frame = b.frame := by
  induction h with
  | pure s f step => exact ⟨derives_redex (pure_readback step ready), rfl, rfl⟩
  | context step saved tail ih =>
    obtain ⟨left, tailOk⟩ := split ready
    have middle := (split left).2
    obtain ⟨h, hs, hf⟩ := ih middle
    exact ⟨derives_context saved h tailOk, hs, hf⟩
  | _ =>
    have checked := tests ready
    simp only [List.forall_mem_append, List.forall_mem_cons,
      supported, Bool.false_eq_true, and_false, false_and] at checked

theorem edge_sound {H : Type} {host : HostSemantics H} {a b : Config H}
    (h : Derives a.code b.code) (hs : a.store = b.store) (hf : a.frame = b.frame) :
    Step host a b := by
  obtain ⟨s, f, before⟩ := a
  obtain ⟨s', f', after⟩ := b
  cases hs
  cases hf
  exact step_sound s f h

theorem steps_sound {H : Type} {host : HostSemantics H} {a b : Config H}
    (path : DerivesPath scalarSyntax a.code b.code) (hs : a.store = b.store) (hf : a.frame = b.frame) :
    Steps host a b := by
  obtain ⟨s, f, before⟩ := a
  obtain ⟨s', f', after⟩ := b
  cases hs
  cases hf
  exact Relation.ReflTransGen.lift (p := Step host) (fun code : List Admin => (⟨s, f, code⟩ : Config H))
    (fun _ _ h => step_sound s f h) _ _ path

theorem steps_readback {H : Type} {host : HostSemantics H} {a b : Config H}
    (h : Steps host a b) (ready : Supported a.code) :
    DerivesPath scalarSyntax a.code b.code ∧ a.store = b.store ∧ a.frame = b.frame := by
  induction h with
  | refl => exact ⟨.refl, rfl, rfl⟩
  | tail _ step ih =>
    obtain ⟨path, hs, hf⟩ := ih
    obtain ⟨edge, hs', hf'⟩ := step_readback step (path_admitted path ready)
    exact ⟨path.tail edge, hs.trans hs', hf.trans hf'⟩

end Silmaril.Wasm.Institution.Operational.LegacyDivision.Lime1.Proofs
