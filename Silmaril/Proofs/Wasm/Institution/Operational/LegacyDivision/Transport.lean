module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.V1.Thms
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Lime1.Thms
public import Silmaril.Wasm.Lime1.Execution.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs

open Silmaril.Wasm.Execution.Runtime

private structure RulesMap {I J : Type} (S : Syntax I) (T : Syntax J) where
  instr : I → J
  value : ∀ v, AdminInstr.map instr (S.value v) = T.value v
  divide : ∀ t sign, AdminInstr.map instr (S.divide t sign) = T.divide t sign
  nop : AdminInstr.map instr S.nop = T.nop

private theorem mapTrap {I J : Type} (f : I → J) :
    AdminInstr.map f .trap = .trap := rfl

private theorem RulesMap.values {I J : Type} {S : Syntax I} {T : Syntax J}
    (F : RulesMap S T) (vs : List Value) :
    (S.values vs).map (AdminInstr.map F.instr) = T.values vs := by
  simp [Syntax.values, List.map_map, Function.comp_def, F.value]

private theorem RulesMap.admitted {I J : Type} {S : Syntax I} {T : Syntax J}
    (F : RulesMap S T) {xs : List (AdminInstr I)} (h : Admitted S xs) :
    Admitted T (xs.map (AdminInstr.map F.instr)) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  have okay := h a ha
  cases okay with
  | value v => rw [F.value]; exact .value v
  | divide t k => rw [F.divide]; exact .divide t k
  | nop => rw [F.nop]; exact .nop
  | trap => exact .trap

private theorem RulesMap.derives {I J : Type} {S : Syntax I} {T : Syntax J}
    (F : RulesMap S T) {xs ys : List (AdminInstr I)} (h : DerivesEdge S xs ys) :
    DerivesEdge T (xs.map (AdminInstr.map F.instr)) (ys.map (AdminInstr.map F.instr)) := by
  apply derives_induction
    (R := fun a b => DerivesEdge T (a.map (AdminInstr.map F.instr)) (b.map (AdminInstr.map F.instr)))
    _ _ h
  · intro before after rule
    cases rule with
    | divide t k x y z ok =>
      simpa only [List.map_cons, List.map_nil, F.value, F.divide] using
        derives_redex (S := T) (.divide t k x y z ok)
    | divTrap t k x y cause trap =>
      simpa only [List.map_cons, List.map_nil, F.value, F.divide, mapTrap] using
        derives_redex (S := T) (.divTrap t k x y cause trap)
    | nop =>
      simpa only [List.map_cons, List.map_nil, F.nop] using derives_redex (S := T) .nop
    | trapValues v vs tail ok =>
      simpa only [List.map_append, F.values, List.map_cons, List.map_nil, mapTrap] using
        derives_redex (S := T) (.trapValues v vs (tail.map _) (F.admitted ok))
    | trapTail i tail ok =>
      have tailOk := F.admitted ok
      exact derives_redex (.trapTail (AdminInstr.map F.instr i) (tail.map _) tailOk)
  · intro saved before after tail middle ok
    simpa only [List.map_append, F.values] using derives_context saved middle (F.admitted ok)

private def toLime : RulesMap V1.scalarSyntax Lime1.scalarSyntax where
  instr := Silmaril.Wasm.V1.Instr.toLime
  value v := by rcases v with ⟨t, bits⟩; cases t <;> rfl
  divide _ _ := rfl
  nop := rfl

/-- The default lives outside the flat guard. On guarded instructions the
public partial inverse returns the corresponding V1 instruction. -/
private def readInstr (i : Silmaril.Wasm.Lime1.Instr) : Silmaril.Wasm.V1.Instr :=
  (Silmaril.Wasm.V1.Instr.ofCore? i.toCore).getD .nop

private def fromLime : RulesMap Lime1.scalarSyntax V1.scalarSyntax where
  instr := readInstr
  value v := by rcases v with ⟨t, bits⟩; cases t <;> rfl
  divide _ _ := rfl
  nop := rfl

private theorem roundtripV1 {a : Silmaril.Wasm.V1.Execution.Admin} (h : Allowed V1.scalarSyntax a) :
    AdminInstr.map readInstr (AdminInstr.map Silmaril.Wasm.V1.Instr.toLime a) = a := by
  change AdminInstr.map fromLime.instr (AdminInstr.map toLime.instr a) = a
  cases h with
  | value v => rw [toLime.value, fromLime.value]
  | divide t k => rw [toLime.divide, fromLime.divide]
  | nop => rw [toLime.nop, fromLime.nop]
  | trap => rfl

private theorem roundtripLime {a : Silmaril.Wasm.Lime1.Execution.Admin}
    (h : Allowed Lime1.scalarSyntax a) :
    AdminInstr.map Silmaril.Wasm.V1.Instr.toLime (AdminInstr.map readInstr a) = a := by
  change AdminInstr.map toLime.instr (AdminInstr.map fromLime.instr a) = a
  cases h with
  | value v => rw [fromLime.value, toLime.value]
  | divide t k => rw [fromLime.divide, toLime.divide]
  | nop => rw [fromLime.nop, toLime.nop]
  | trap => rfl

private theorem roundtripCodeV1 {xs : List Silmaril.Wasm.V1.Execution.Admin} (h : V1.Supported xs) :
    (Silmaril.Wasm.V1.Execution.codeToLime xs).map (AdminInstr.map readInstr) = xs := by
  simp only [Silmaril.Wasm.V1.Execution.codeToLime, AdminInstr.mapList_eq_map, List.map_map]
  exact (List.map_congr_left (g := id) fun a ha => roundtripV1 (h a ha)).trans (List.map_id xs)

private theorem roundtripCodeLime {xs : List Silmaril.Wasm.Lime1.Execution.Admin}
    (h : Lime1.Supported xs) :
    Silmaril.Wasm.V1.Execution.codeToLime (xs.map (AdminInstr.map readInstr)) = xs := by
  simp only [Silmaril.Wasm.V1.Execution.codeToLime, AdminInstr.mapList_eq_map, List.map_map]
  exact (List.map_congr_left (g := id) fun a ha => roundtripLime (h a ha)).trans (List.map_id xs)

theorem translated_supported {xs : List Silmaril.Wasm.V1.Execution.Admin} (h : V1.Supported xs) :
    Lime1.Supported (Silmaril.Wasm.V1.Execution.codeToLime xs) := by
  simpa only [Silmaril.Wasm.V1.Execution.codeToLime, AdminInstr.mapList_eq_map] using
    (show Lime1.Supported (xs.map (AdminInstr.map Silmaril.Wasm.V1.Instr.toLime)) from
      toLime.admitted h)

theorem translated_step {H : Type} {src : Silmaril.Wasm.V1.Execution.HostSemantics H}
    {dst : Silmaril.Wasm.Lime1.Execution.HostSemantics H} {a b : Silmaril.Wasm.V1.Execution.Config H}
    (ready : V1.Supported a.code) (step : Silmaril.Wasm.V1.Execution.Step src a b) :
    Silmaril.Wasm.Lime1.Execution.Step dst a.toLime b.toLime := by
  obtain ⟨rule, hs, hf⟩ := V1.step_readback ready step
  have translated : Lime1.Derives a.toLime.code b.toLime.code := by
    simpa only [Silmaril.Wasm.V1.Execution.Config.toLime,
      Silmaril.Wasm.V1.Execution.codeToLime, AdminInstr.mapList_eq_map, toLime] using
      toLime.derives rule
  exact (Lime1.step_iff (translated_supported ready)).mpr
    ⟨translated, congrArg (Store.mapCode Silmaril.Wasm.V1.Func.toLime) hs, hf⟩

theorem translated_step_readback {H : Type} {src : Silmaril.Wasm.V1.Execution.HostSemantics H}
    {dst : Silmaril.Wasm.Lime1.Execution.HostSemantics H} {a : Silmaril.Wasm.V1.Execution.Config H}
    {b : Silmaril.Wasm.Lime1.Execution.Config H}
    (ready : V1.Supported a.code) (step : Silmaril.Wasm.Lime1.Execution.Step dst a.toLime b) :
    ∃ c : Silmaril.Wasm.V1.Execution.Config H, Silmaril.Wasm.V1.Execution.Step src a c ∧ c.toLime = b := by
  obtain ⟨rule, hs, hf⟩ := Lime1.step_readback (translated_supported ready) step
  have derived := fromLime.derives rule
  change V1.Derives ((Silmaril.Wasm.V1.Execution.codeToLime a.code).map (AdminInstr.map readInstr))
    (b.code.map (AdminInstr.map readInstr)) at derived
  rw [roundtripCodeV1 ready] at derived
  refine ⟨⟨a.store, a.frame, _⟩, V1.step_sound a.store a.frame derived, ?_⟩
  change Config.mk _ _ (Silmaril.Wasm.V1.Execution.codeToLime _) = b
  rw [roundtripCodeLime (derives_admitted rule).2]
  cases b
  cases hs
  cases hf
  rfl

theorem translated_steps {H : Type} {src : Silmaril.Wasm.V1.Execution.HostSemantics H}
    {dst : Silmaril.Wasm.Lime1.Execution.HostSemantics H} {a b : Silmaril.Wasm.V1.Execution.Config H}
    (ready : V1.Supported a.code) (path : Silmaril.Wasm.V1.Execution.Steps src a b) :
    Silmaril.Wasm.Lime1.Execution.Steps dst a.toLime b.toLime := by
  induction path with
  | refl => exact .refl
  | tail prior step ih =>
    exact ih.tail (translated_step (path_admitted ((V1.steps_iff ready).mp prior).1 ready) step)

theorem translated_steps_readback {H : Type} {src : Silmaril.Wasm.V1.Execution.HostSemantics H}
    {dst : Silmaril.Wasm.Lime1.Execution.HostSemantics H} {a : Silmaril.Wasm.V1.Execution.Config H}
    {b : Silmaril.Wasm.Lime1.Execution.Config H}
    (ready : V1.Supported a.code) (path : Silmaril.Wasm.Lime1.Execution.Steps dst a.toLime b) :
    ∃ c : Silmaril.Wasm.V1.Execution.Config H, Silmaril.Wasm.V1.Execution.Steps src a c ∧ c.toLime = b := by
  induction path with
  | refl => exact ⟨a, .refl, rfl⟩
  | tail _ step ih =>
    obtain ⟨c, prior, rfl⟩ := ih
    have supported := path_admitted ((V1.steps_iff ready).mp prior).1 ready
    obtain ⟨t, edge, rfl⟩ := translated_step_readback (src := src) supported step
    exact ⟨t, prior.tail edge, rfl⟩

theorem emit_code_commutes (xs : List Silmaril.Wasm.V1.Execution.Admin) :
    emitCode Lime1.coreEncoding.emit (Silmaril.Wasm.V1.Execution.codeToLime xs) =
      emitCode V1.coreEncoding.emit xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have head : emitAdmin Lime1.coreEncoding.emit
        (AdminInstr.map Silmaril.Wasm.V1.Instr.toLime a) = emitAdmin V1.coreEncoding.emit a := by
      cases a <;> simp [AdminInstr.map, emitAdmin, Lime1.coreEncoding, V1.coreEncoding]
    simp only [Silmaril.Wasm.V1.Execution.codeToLime_cons, emitCode, List.filterMap_cons, head]
    simp only [emitCode] at ih
    rw [ih]

end Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs
