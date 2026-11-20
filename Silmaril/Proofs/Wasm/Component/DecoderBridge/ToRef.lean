module

public import Silmaril.Wasm.Component.DecoderBridge.Defs

/-!
# The REF reading: what `Conformance.toRef` does with core modules and core instantiations

`toRef_ok`: if `Conformance.toRef a = .ok r` and no top-level import, alias or export of `a`
has the core module sort, then the core module index space of `r` is the core decoder's reading
of the bytes of `a`'s core module sections, in order, and the core instantiations of `r` are
those of `a`. Section by section (`section_ok`): every definition `toRef` produces other than
core modules and core instantiations is `Neutral` (it adds to neither).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge

/-- A reference definition over Core 3.0 modules. -/
abbrev RDef := Syntax.Definition Silmaril.Wasm.Module

theorem coreModSpace_cons (d : RDef) (ds : List RDef) :
    coreModSpace (d :: ds) = coreModSpace [d] ++ coreModSpace ds := by
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, d⟩ | _ | _ <;>
    first | rfl | (cases d <;> rfl) | (simp only [coreModSpace]; split <;> simp)

theorem refInsts_cons (d : RDef) (ds : List RDef) :
    refInsts (d :: ds) = refInsts [d] ++ refInsts ds := by
  rcases d with _ | e | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> first | rfl | (cases e <;> rfl)

theorem coreModSpace_append (p q : List RDef) :
    coreModSpace (p ++ q) = coreModSpace p ++ coreModSpace q := by
  induction p with
  | nil => rfl
  | cons d p ih => rw [List.cons_append, coreModSpace_cons, ih, coreModSpace_cons d p, List.append_assoc]

theorem refInsts_append (p q : List RDef) : refInsts (p ++ q) = refInsts p ++ refInsts q := by
  induction p with
  | nil => rfl
  | cons d p ih => rw [List.cons_append, refInsts_cons, ih, refInsts_cons d p, List.append_assoc]

/-- A definition adds nothing to the core module space nor to the core instantiations. -/
def Neutral (d : RDef) : Prop := coreModSpace [d] = [] ∧ refInsts [d] = []

theorem neutral_list : ∀ {ds : List RDef}, (∀ d ∈ ds, Neutral d) → coreModSpace ds = [] ∧ refInsts ds = []
  | [], _ => ⟨rfl, rfl⟩
  | d :: ds, h => by
    obtain ⟨h1, h2⟩ := h d (by simp)
    obtain ⟨h3, h4⟩ := neutral_list (ds := ds) fun d hd => h d (by simp [hd])
    rw [coreModSpace_cons, refInsts_cons, h1, h2, h3, h4]; exact ⟨rfl, rfl⟩

theorem mapM_ok {α β ε} {f : α → Except ε β} : ∀ {xs : List α} {ys : List β},
    xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i y hy
      split at h
      · cases h
      · rename_i ys' hys
        cases h
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨x, by simp, hy⟩
        · obtain ⟨w, hw, hw'⟩ := mapM_ok hys z hz
          exact ⟨w, by simp [hw], hw'⟩

theorem sort_ne {x : Binary.ItemSort} (h : (x != .core .module) = true) :
    ToRef.sort x ≠ .core .module_ := by
  rcases x with c | _ | _ | _ | _ | _
  · cases c <;> simp_all [ToRef.sort, ToRef.coreSort]
  all_goals simp [ToRef.sort]

theorem aliasDef_sort {a : Binary.Alias} {b} (h : ToRef.aliasDef a = .ok b) :
    aliasSort b = ToRef.sort a.sort := by
  rcases a with ⟨srt, tgt⟩
  cases tgt <;> cases srt <;> simp only [ToRef.aliasDef] at h <;> cases h <;> rfl

theorem toRef_section_ok {sec : Binary.Section} {ds : List RDef} (h : ToRef.section_ sec = .ok ds)
    (hn : sectionNoModuleSort sec = true) :
    coreModSpace ds = (modBytes [sec]).map Silmaril.Wasm.Binary.Core.decode? ∧
      refInsts ds = instExprs [sec] := by
  cases sec with
  | coreModule bs =>
    simp only [ToRef.section_, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i m hm
      cases h
      unfold ToRef.coreModule at hm
      split at hm
      · rename_i d hd; cases hm; simp [coreModSpace, refInsts, modBytes, instExprs, hd]
      · cases hm
  | coreInstances xs =>
    simp only [ToRef.section_] at h
    cases h
    simp only [modBytes, instExprs, List.map_nil, List.append_nil]
    clear hn
    induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons x xs ih =>
      rw [List.map_cons, coreModSpace_cons, refInsts_cons, ih.1, ih.2]
      cases x <;> simp [ToRef.coreInstanceExpr, coreModSpace, refInsts, instExpr?, List.filterMap_cons]
  | custom n d => cases h; exact ⟨rfl, rfl⟩
  | coreTypes xs =>
    have := neutral_list (ds := ds) fun d hd => by
      obtain ⟨x, -, hx⟩ := mapM_ok h d hd
      cases hc : ToRef.coreType x <;> simp [hc, Functor.map, Except.map] at hx
      subst hx; exact ⟨rfl, rfl⟩
    simpa [modBytes, instExprs] using this
  | component c =>
    simp only [ToRef.section_, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  | instances xs =>
    cases h
    have := neutral_list (ds := xs.map fun x => .instance_ (ToRef.instanceExpr x)) fun d hd => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; exact ⟨rfl, rfl⟩
    simpa [modBytes, instExprs] using this
  | aliases xs =>
    have := neutral_list (ds := ds) fun d hd => by
      obtain ⟨x, hxs, hx⟩ := mapM_ok h d hd
      cases hc : ToRef.aliasDef x <;> simp [hc, Functor.map, Except.map] at hx
      subst hx
      rename_i b
      have hs := sort_ne (by
        simp only [sectionNoModuleSort, List.all_eq_true] at hn; exact hn x hxs)
      rw [← aliasDef_sort hc] at hs
      simp [Neutral, coreModSpace, refInsts, hs]
    simpa [modBytes, instExprs] using this
  | types xs =>
    have := neutral_list (ds := ds) fun d hd => by
      obtain ⟨x, -, hx⟩ := mapM_ok h d hd
      cases hc : ToRef.defType x <;> simp [hc, Functor.map, Except.map] at hx
      subst hx; exact ⟨rfl, rfl⟩
    simpa [modBytes, instExprs] using this
  | canons xs =>
    cases h
    have := neutral_list (ds := xs.map fun x => .canon (ToRef.canon x)) fun d hd => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; exact ⟨rfl, rfl⟩
    simpa [modBytes, instExprs] using this
  | start st => cases h; exact ⟨rfl, rfl⟩
  | imports xs =>
    cases h
    have := neutral_list (ds := xs.map fun x => .import_ (ToRef.externName x.name) (ToRef.externDesc x.desc))
      fun d hd => by
        obtain ⟨x, hxs, rfl⟩ := List.mem_map.1 hd
        simp only [sectionNoModuleSort, List.all_eq_true] at hn
        have := hn x hxs
        revert this
        cases x.desc <;> simp [Neutral, coreModSpace, refInsts, ToRef.externDesc]
    simpa [modBytes, instExprs] using this
  | exports xs =>
    cases h
    have := neutral_list (ds := xs.map fun x =>
        .export_ (ToRef.externName x.name) (ToRef.sortIdx x.item) (x.desc.map ToRef.externDesc))
      fun d hd => by
        obtain ⟨x, hxs, rfl⟩ := List.mem_map.1 hd
        simp only [sectionNoModuleSort, List.all_eq_true] at hn
        have hs := sort_ne (hn x hxs)
        simp [Neutral, coreModSpace, refInsts, ToRef.sortIdx, hs]
    simpa [modBytes, instExprs] using this
  | values xs =>
    cases h
    have := neutral_list (ds := xs.map fun x => .value (ToRef.valType x.type) x.bytes.toList)
      fun d hd => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; exact ⟨rfl, rfl⟩
    simpa [modBytes, instExprs] using this

theorem modBytes_cons' (s : Binary.Section) (ss : List Binary.Section) :
    modBytes (s :: ss) = modBytes [s] ++ modBytes ss := by cases s <;> rfl

theorem instExprs_cons (s : Binary.Section) (ss : List Binary.Section) :
    instExprs (s :: ss) = instExprs [s] ++ instExprs ss := by cases s <;> simp [instExprs]

theorem toRef_sections_ok : ∀ {ss : List Binary.Section} {ds : List RDef}, ToRef.sections ss = .ok ds →
    noModuleSort ss = true →
    coreModSpace ds = (modBytes ss).map Silmaril.Wasm.Binary.Core.decode? ∧ refInsts ds = instExprs ss
  | [], ds, h, _ => by simp only [ToRef.sections] at h; cases h; exact ⟨rfl, rfl⟩
  | s :: ss, ds, h, hn => by
    simp only [ToRef.sections, bind, Except.bind, pure, Except.pure] at h
    simp only [noModuleSort, List.all_cons, Bool.and_eq_true] at hn
    split at h
    · cases h
    · rename_i d1 h1
      split at h
      · cases h
      · rename_i d2 h2
        cases h
        obtain ⟨a1, b1⟩ := toRef_section_ok h1 hn.1
        obtain ⟨a2, b2⟩ := toRef_sections_ok h2 hn.2
        rw [coreModSpace_append, refInsts_append, a1, a2, b1, b2, modBytes_cons' s ss, instExprs_cons s ss,
          List.map_append]
        exact ⟨rfl, rfl⟩

theorem toRef_ok {a : Binary.Ast} {r : RefComponent} (h : toRef a = .ok r)
    (hn : noModuleSort a.sections = true) :
    coreModSpace r = (modBytes a.sections).map Silmaril.Wasm.Binary.Core.decode? ∧
      refInsts r = instExprs a.sections := by
  cases a with
  | mk ss => exact toRef_sections_ok (ss := ss) (by simpa [toRef, ToRef.ast] using h) hn

end Silmaril.Proofs.Wasm.Component.DecoderBridge
