module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Defs

/-!
# List components read from their bytes: proofs

`toRef_toAst`: for **every** list component `c` (`ListLift.ListComp`) and core module bytes
`core` that decode to `c.mod`, the reference reading `toRef?` of the emitted binary component
`c.toAst core` is `c.toRef`. The emitted sections are read section by section:

* the core module by the decoder; the core instance, the aliases, the canonical lifts and the
  function exports by `section_`'s conversions;
* the type sections (`tySections (typeDefsB c.exports 0)`) item by item (`tySections_flat`):
  every maximal run of type definitions is one `types` section and every run of type exports
  one `exports` section, so the flattened reading is the reading of the items in order; and the
  binary items of each type (`LTy.emitB`) read as the reference definitions of `LTy.emit`
  (`emitB_ok`, by mutual induction on the types, with the same value types and type indices).

`toRef_of_parse`: hence every reference reading of what bytes parsing to `c.toAst core` parse
to is `c.toRef`. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmComponents.Acceptor

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Project.WasmComponents.Ref

/-- The flattened reading of a list of sections. -/
def flat (ss : List Binary.Section) : Option (List (Syntax.Definition Silmaril.Wasm.Module)) :=
  (ss.mapM section_).map List.flatten

theorem flat_nil : flat [] = some [] := rfl

theorem flat_cons (x : Binary.Section) (ss : List Binary.Section) :
    flat (x :: ss) = (section_ x).bind fun a => (flat ss).map (a ++ ·) := by
  unfold flat
  rw [List.mapM_cons]
  cases section_ x <;> cases ss.mapM section_ <;> rfl

theorem flat_append (l₁ l₂ : List Binary.Section) :
    flat (l₁ ++ l₂) = (flat l₁).bind fun a => (flat l₂).map (a ++ ·) := by
  induction l₁ with
  | nil => simp [flat_nil]
  | cons x l ih =>
    rw [List.cons_append, flat_cons, flat_cons, ih]
    cases section_ x <;> cases flat l <;> cases flat l₂ <;> simp

/-- The reading of one binary type item. -/
def itemRef : TyItem → Option (Syntax.Definition Silmaril.Wasm.Module)
  | .def_ d => (defType d).map .type
  | .export_ n i => some (export_ ⟨↑n, ⟨.type, i⟩, none⟩)

theorem mapM_itemRef_cons (x : TyItem) (l : List TyItem) :
    (x :: l).mapM itemRef = (itemRef x).bind fun a => (l.mapM itemRef).map (a :: ·) := by
  rw [List.mapM_cons]
  cases itemRef x <;> cases l.mapM itemRef <;> rfl

theorem flat_types_cons (d : Binary.DefType) (ds : List Binary.DefType) (ss : List Binary.Section) :
    flat (.types (d :: ds) :: ss) =
      (itemRef (.def_ d)).bind fun a => (flat (.types ds :: ss)).map (a :: ·) := by
  rw [flat_cons, flat_cons]
  simp only [section_, itemRef, List.mapM_cons]
  cases defType d <;> cases ds.mapM defType <;> cases flat ss <;> rfl

theorem flat_types_nil (ss : List Binary.Section) : flat (.types [] :: ss) = flat ss := by
  rw [flat_cons]
  cases flat ss <;> rfl

theorem flat_exports_cons (e : Binary.Export) (es : List Binary.Export) (ss : List Binary.Section) :
    flat (.exports (e :: es) :: ss) =
      (some (export_ e)).bind fun a => (flat (.exports es :: ss)).map (a :: ·) := by
  rw [flat_cons, flat_cons]
  simp only [section_, List.map_cons]
  cases flat ss <;> rfl

theorem flat_exports_nil (ss : List Binary.Section) : flat (.exports [] :: ss) = flat ss := by
  rw [flat_cons]
  cases flat ss <;> rfl

/-- **The type sections read as their items.** -/
theorem tySections_flat : ∀ is : List TyItem, flat (tySections is) = is.mapM itemRef
  | [] => rfl
  | .def_ d :: is => by
    rw [mapM_itemRef_cons, ← tySections_flat is]
    simp only [tySections]
    split
    · rename_i ds ss h
      rw [flat_types_cons, h]
    · rw [flat_types_cons, flat_types_nil]
  | .export_ n i :: is => by
    rw [mapM_itemRef_cons, ← tySections_flat is]
    simp only [tySections]
    split
    · rename_i es ss h
      rw [flat_exports_cons, h]
      rfl
    · rw [flat_exports_cons, flat_exports_nil]
      rfl

/-! ## The types -/

/-- The binary emission `b` of a type reads as the reference emission `r`: the items read as the
definitions, the value types agree and so do the next free type indices. -/
def EmitOk (b : Binary.ValType × List TyItem × Nat)
    (r : Syntax.VT × List (Syntax.Definition Silmaril.Wasm.Module) × Nat) : Prop :=
  b.2.1.mapM itemRef = some r.2.1 ∧ valType b.1 = r.1 ∧ b.2.2 = r.2.2

theorem mapM_itemRef_append (l₁ l₂ : List TyItem) :
    (l₁ ++ l₂).mapM itemRef = (l₁.mapM itemRef).bind fun a => (l₂.mapM itemRef).map (a ++ ·) := by
  induction l₁ with
  | nil => simp
  | cons x l ih =>
    rw [List.cons_append, mapM_itemRef_cons, mapM_itemRef_cons, ih]
    cases itemRef x <;> cases l.mapM itemRef <;> cases l₂.mapM itemRef <;> simp

mutual
theorem emitB_ok : ∀ (t : LTy) (n : Nat), EmitOk (t.emitB n) (t.emit n)
  | .s32, _ => ⟨rfl, rfl, rfl⟩
  | .u32, _ => ⟨rfl, rfl, rfl⟩
  | .s64, _ => ⟨rfl, rfl, rfl⟩
  | .list t, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitB_ok t n
    simp only [EmitOk, LTy.emitB, LTy.emit]
    revert h₁ h₂ h₃
    rcases t.emitB n with ⟨v, ds, k⟩
    rcases t.emit (M := Silmaril.Wasm.Module) n with ⟨v', ds', k'⟩
    rintro h₁ h₂ rfl
    simp only at h₁ h₂
    subst h₂
    refine ⟨?_, rfl, rfl⟩
    rw [mapM_itemRef_append, h₁]
    simp [itemRef, defType, defValType]
  | .tuple t ts, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitB_ok t n
    simp only [EmitOk, LTy.emitB, LTy.emit]
    revert h₁ h₂ h₃
    rcases t.emitB n with ⟨v, ds, k⟩
    rcases t.emit (M := Silmaril.Wasm.Module) n with ⟨v', ds', k'⟩
    rintro h₁ h₂ rfl
    obtain ⟨g₁, g₂, g₃⟩ := emitListB_ok ts k
    revert g₁ g₂ g₃
    rcases LTy.emitListB ts k with ⟨vs, es, m⟩
    rcases LTy.emitList (M := Silmaril.Wasm.Module) ts k with ⟨vs', es', m'⟩
    rintro g₁ g₂ rfl
    simp only at h₁ h₂ g₁ g₂
    subst h₂ g₂
    refine ⟨?_, rfl, rfl⟩
    rw [mapM_itemRef_append, mapM_itemRef_append, h₁, g₁]
    simp [itemRef, defType, defValType]
  | .record name l t fs, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitB_ok t n
    simp only [EmitOk, LTy.emitB, LTy.emit]
    revert h₁ h₂ h₃
    rcases t.emitB n with ⟨v, ds, k⟩
    rcases t.emit (M := Silmaril.Wasm.Module) n with ⟨v', ds', k'⟩
    rintro h₁ h₂ rfl
    obtain ⟨g₁, g₂, g₃⟩ := emitFieldsB_ok fs k
    revert g₁ g₂ g₃
    rcases LTy.emitFieldsB fs k with ⟨vs, es, m⟩
    rcases LTy.emitFields (M := Silmaril.Wasm.Module) fs k with ⟨vs', es', m'⟩
    rintro g₁ g₂ rfl
    simp only at h₁ h₂ g₁ g₂
    subst h₂ g₂
    refine ⟨?_, rfl, rfl⟩
    rw [mapM_itemRef_append, mapM_itemRef_append, h₁, g₁]
    simp [itemRef, defType, defValType, export_, externName, sortIdx, sort]

theorem emitListB_ok : ∀ (ts : List LTy) (n : Nat),
    (LTy.emitListB ts n).2.1.mapM itemRef =
        some (LTy.emitList (M := Silmaril.Wasm.Module) ts n).2.1 ∧
      (LTy.emitListB ts n).1.map valType = (LTy.emitList (M := Silmaril.Wasm.Module) ts n).1 ∧
      (LTy.emitListB ts n).2.2 = (LTy.emitList (M := Silmaril.Wasm.Module) ts n).2.2
  | [], _ => ⟨rfl, rfl, rfl⟩
  | t :: ts, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitB_ok t n
    simp only [LTy.emitListB, LTy.emitList]
    revert h₁ h₂ h₃
    rcases t.emitB n with ⟨v, ds, k⟩
    rcases t.emit (M := Silmaril.Wasm.Module) n with ⟨v', ds', k'⟩
    rintro h₁ h₂ rfl
    obtain ⟨g₁, g₂, g₃⟩ := emitListB_ok ts k
    revert g₁ g₂ g₃
    rcases LTy.emitListB ts k with ⟨vs, es, m⟩
    rcases LTy.emitList (M := Silmaril.Wasm.Module) ts k with ⟨vs', es', m'⟩
    rintro g₁ g₂ rfl
    refine ⟨?_, by simp only [List.map_cons]; rw [h₂, g₂], rfl⟩
    rw [mapM_itemRef_append, h₁, g₁]
    rfl

theorem emitFieldsB_ok : ∀ (fs : List (String × LTy)) (n : Nat),
    (LTy.emitFieldsB fs n).2.1.mapM itemRef =
        some (LTy.emitFields (M := Silmaril.Wasm.Module) fs n).2.1 ∧
      (LTy.emitFieldsB fs n).1.map (fun f => (f.1, valType f.2)) =
        (LTy.emitFields (M := Silmaril.Wasm.Module) fs n).1 ∧
      (LTy.emitFieldsB fs n).2.2 = (LTy.emitFields (M := Silmaril.Wasm.Module) fs n).2.2
  | [], _ => ⟨rfl, rfl, rfl⟩
  | (l, t) :: fs, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitB_ok t n
    simp only [LTy.emitFieldsB, LTy.emitFields]
    revert h₁ h₂ h₃
    rcases t.emitB n with ⟨v, ds, k⟩
    rcases t.emit (M := Silmaril.Wasm.Module) n with ⟨v', ds', k'⟩
    rintro h₁ h₂ rfl
    obtain ⟨g₁, g₂, g₃⟩ := emitFieldsB_ok fs k
    revert g₁ g₂ g₃
    rcases LTy.emitFieldsB fs k with ⟨vs, es, m⟩
    rcases LTy.emitFields (M := Silmaril.Wasm.Module) fs k with ⟨vs', es', m'⟩
    rintro g₁ g₂ rfl
    refine ⟨?_, by simp only [List.map_cons]; rw [h₂, g₂], rfl⟩
    rw [mapM_itemRef_append, h₁, g₁]
    rfl
end

theorem emitParamsB_ok : ∀ (ps : List (String × LTy)) (n : Nat),
    (emitParamsB ps n).2.1.mapM itemRef = some (emitParams (M := Silmaril.Wasm.Module) ps n).2.1 ∧
      (emitParamsB ps n).1.map (fun f => (f.1, valType f.2)) =
        (emitParams (M := Silmaril.Wasm.Module) ps n).1 ∧
      (emitParamsB ps n).2.2 = (emitParams (M := Silmaril.Wasm.Module) ps n).2.2
  | [], _ => ⟨rfl, rfl, rfl⟩
  | (x, t) :: ps, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitB_ok t n
    simp only [emitParamsB, emitParams]
    revert h₁ h₂ h₃
    rcases t.emitB n with ⟨v, ds, k⟩
    rcases t.emit (M := Silmaril.Wasm.Module) n with ⟨v', ds', k'⟩
    rintro h₁ h₂ rfl
    obtain ⟨g₁, g₂, g₃⟩ := emitParamsB_ok ps k
    revert g₁ g₂ g₃
    rcases emitParamsB ps k with ⟨vs, es, m⟩
    rcases emitParams (M := Silmaril.Wasm.Module) ps k with ⟨vs', es', m'⟩
    rintro g₁ g₂ rfl
    refine ⟨?_, by simp only [List.map_cons]; rw [h₂, g₂], rfl⟩
    rw [mapM_itemRef_append, h₁, g₁]
    rfl

theorem typeDefsB_ok : ∀ (xs : List ListExport) (n : Nat),
    (ListComp.typeDefsB xs n).mapM itemRef =
      some (ListComp.typeDefs (M := Silmaril.Wasm.Module) xs n)
  | [], _ => rfl
  | x :: xs, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitParamsB_ok x.params n
    simp only [ListComp.typeDefsB, ListComp.typeDefs]
    revert h₁ h₂ h₃
    rcases emitParamsB x.params n with ⟨vs, ds, k⟩
    rcases emitParams (M := Silmaril.Wasm.Module) x.params n with ⟨vs', ds', k'⟩
    rintro h₁ h₂ rfl
    simp only at h₁ h₂
    subst h₂
    rw [mapM_itemRef_append, mapM_itemRef_append, h₁, typeDefsB_ok xs (k + 1)]
    simp [itemRef, defType, funcType]
    rfl

/-! ## The component -/

theorem mapM_some {α β : Type} (f : α → β) :
    ∀ xs : List α, xs.mapM (fun x => some (f x)) = some (xs.map f)
  | [] => rfl
  | x :: xs => by simp [List.mapM_cons, mapM_some f xs]

/-- **The reference reading of every emitted list component** is its reference component. -/
theorem toRef_toAst (c : ListComp) {core : ByteArray}
    (h : Silmaril.Wasm.Binary.Core.decode? core = some c.mod) :
    toRef? (c.toAst core) = some c.toRef := by
  have e : toRef? (c.toAst core) = flat (c.toAst core).sections := rfl
  rw [e]
  simp only [ListComp.toAst, Binary.Ast.sections]
  rw [flat_append, flat_append, tySections_flat, typeDefsB_ok]
  simp [flat, List.mapM_cons, section_, h, coreInstance, mapM_some, alias_, coreSort,
    ListComp.toRef, List.map_map, Function.comp_def, canon, canonOpt, export_, externName, sortIdx,
    sort]

/-- **Every reference reading of what the bytes parse to** is the reference component. -/
theorem toRef_of_parse (c : ListComp) {core bytes : ByteArray}
    (hdec : Silmaril.Wasm.Binary.Core.decode? core = some c.mod)
    (hparse : Binary.parse bytes = .ok (c.toAst core)) {ast : Binary.Ast}
    (hp : Binary.parse bytes = .ok ast) {r : Silmaril.Wasm.Component.Reference.Core3Component}
    (hr : toRef? ast = some r) : r = c.toRef := by
  rw [hparse] at hp
  cases hp
  rw [toRef_toAst c hdec] at hr
  cases hr
  rfl

end Silmaril.Proofs.Project.WasmComponents.Acceptor
