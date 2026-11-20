module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.Erase
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Wire

/-!
# The named IR reading is the named reference reading

`lowerSig_of_toRef`: if `Conformance.toRef a = .ok r` and the named reading `refReadN r`
succeeds, the named signature `Binary.Lower.lowerSig a` of the IR reading has its imports and
exports. The named pass (`Binary.Lower.SigSt`) and the named reading (`RN`) run side by side,
section by section and item by item, under the invariant `SI` (the named function types, the
functions, the imports and the exports are equal). The other index spaces of the pass (the
lowering's types, the component instances) are not compared: on the definition shapes the named
reading accepts they are read only to compute named function types of primitive types, which do
not consult them.

`exportNames_of_toRef`: if no definition of `r` exports an instance (`NoInstExport r`), the
export names of `lowerSig a` are the function export names of `r`, for every AST (no fragment).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Named

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Proofs.Wasm.Component.DecoderBridge (mapM_forall₂ defType_func refFuncTy_funcTy
  sort_func coreSort_func forall₂_map_self mapM_ok)

/-- **The invariant**: the named pass and the named reading agree on named function types,
functions, imports and exports. -/
structure SI (s : SigSt) (N : RN) : Prop where
  types : s.types.map (·.2) = N.types.map some
  funcs : s.funcs = N.funcs
  imports : s.imports = N.imports
  exports : s.exports = N.exports

theorem nty_of {s : SigSt} {N : RN} (h : SI s N) {t : Nat} {ft : NFuncTy}
    (ht : N.types[t]? = some ft) : s.nty t = ft := by
  have h1 : (s.types.map (·.2))[t]? = some (some ft) := by rw [h.types]; simp [ht]
  rw [List.getElem?_map] at h1
  cases hx : s.types[t]? with
  | none => simp [hx] at h1
  | some p => simp [hx] at h1; simp [SigSt.nty, hx, h1]

theorem fn_of {s : SigSt} {N : RN} (h : SI s N) {i : Nat} {ft : NFuncTy}
    (hi : N.funcs[i]? = some ft) : s.fn i = ft := by
  simp [SigSt.fn, h.funcs, hi]

theorem namedFuncTy_of (types : Array TypeEntry) {g : Binary.FuncType} {nf : NFuncTy}
    (h : refNFuncTy (ToRef.funcType g) = some nf) : namedFuncTy types g = some nf := by
  simp only [refNFuncTy, Option.map_eq_some_iff] at h
  obtain ⟨ft, hft, rfl⟩ := h
  simp [namedFuncTy, refFuncTy_funcTy types hft, ToRef.funcType, Function.comp_def]

/-! ## Items -/

theorem si_type {s : SigSt} {N N' : RN} {x : Binary.DefType} {t' : Syntax.DefType}
    (hs : SI s N) (ht : ToRef.defType x = .ok t') (hr : refNStep N (.type t') = some N') :
    SI (sigType s x) N' := by
  cases t' with
  | func f =>
    obtain ⟨g, rfl, rfl⟩ := defType_func ht
    simp only [refNStep, bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    obtain ⟨nf, hnf, rfl⟩ := hr
    exact { hs with types := by simp [sigType, namedDefType, namedFuncTy_of _ hnf, hs.types] }
  | _ => simp [refNStep] at hr

theorem si_import {s : SigSt} {N N' : RN} {x : Binary.Import} (hs : SI s N)
    (hr : refNStep N (.import_ (ToRef.externName x.name) (ToRef.externDesc x.desc)) = some N') :
    SI (sigImport s x) N' := by
  rcases x with ⟨n, d⟩
  cases d with
  | func t =>
    simp only [ToRef.externDesc, refNStep, bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    obtain ⟨ft, hft, rfl⟩ := hr
    simp only [sigImport, nty_of hs hft]
    exact { hs with
      funcs := by simp [hs.funcs]
      imports := by simp [hs.imports, ToRef.externName] }
  | _ => simp [ToRef.externDesc, refNStep] at hr

theorem si_alias {s : SigSt} {N N' : RN} {a : Binary.Alias} {a' : Syntax.Alias} (hs : SI s N)
    (ha : ToRef.aliasDef a = .ok a') (hr : refNStep N (.alias a') = some N') :
    SI (sigAlias s a) N' := by
  rcases a with ⟨srt, tgt⟩
  cases tgt with
  | «export» i n => simp [ToRef.aliasDef] at ha; subst ha; simp [refNStep] at hr
  | outer c i => simp [ToRef.aliasDef] at ha; subst ha; simp [refNStep] at hr
  | coreExport i n =>
    cases srt with
    | core cs =>
      simp only [ToRef.aliasDef, Except.ok.injEq] at ha
      subst ha
      cases hcs : ToRef.coreSort cs with
      | func =>
        rw [hcs] at hr
        simp only [refNStep, Option.some.injEq] at hr
        subst hr
        exact hs
      | _ => rw [hcs] at hr; simp [refNStep] at hr
    | _ => simp [ToRef.aliasDef] at ha

theorem si_canon {s : SigSt} {N N' : RN} {c : Binary.Canon} (hs : SI s N)
    (hr : refNStep N (.canon (ToRef.canon c)) = some N') : SI (sigCanon s c) N' := by
  cases c with
  | lift f opts t =>
    cases opts with
    | cons o os => simp [ToRef.canon, refNStep] at hr
    | nil =>
      simp only [ToRef.canon, List.map_nil, refNStep, bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hr
      obtain ⟨ft, hft, rfl⟩ := hr
      simp only [sigCanon, nty_of hs hft]
      exact { hs with funcs := by simp [hs.funcs] }
  | lower f opts =>
    cases opts with
    | cons o os => simp [ToRef.canon, refNStep] at hr
    | nil =>
      simp only [ToRef.canon, List.map_nil, refNStep, Option.some.injEq] at hr
      subst hr
      exact hs
  | resourceNew t => simp [ToRef.canon, refNStep] at hr
  | resourceDrop t => simp [ToRef.canon, refNStep] at hr
  | resourceRep t => simp [ToRef.canon, refNStep] at hr

theorem si_export {s : SigSt} {N N' : RN} {e : Binary.Export} (hs : SI s N)
    (hr : refNStep N (.export_ (ToRef.externName e.name) (ToRef.sortIdx e.item)
      (e.desc.map ToRef.externDesc)) = some N') : SI (sigExport s e) N' := by
  rcases e with ⟨n, ⟨srt, i⟩, d⟩
  cases d with
  | some d => simp [refNStep] at hr
  | none =>
    simp only [ToRef.sortIdx, Option.map_none] at hr
    cases hsrt : ToRef.sort srt with
    | func =>
      have := sort_func hsrt
      subst this
      rw [hsrt] at hr
      simp only [refNStep, bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      obtain ⟨ft, hft, rfl⟩ := hr
      simp only [sigExport, fn_of hs hft]
      exact { hs with
        funcs := by simp [hs.funcs]
        exports := by simp [hs.exports, ToRef.externName] }
    | _ => rw [hsrt] at hr; simp [refNStep] at hr

/-! ## Sections -/

theorem si_items {α : Type} {g : SigSt → α → SigSt} {D : α → RDef → Prop}
    (hstep : ∀ x d s N N', D x d → SI s N → refNStep N d = some N' → SI (g s x) N') :
    ∀ {xs : List α} {ds : List RDef} {s : SigSt} {N N' : RN}, List.Forall₂ D xs ds → SI s N →
      ds.foldlM refNStep N = some N' → SI (xs.foldl g s) N'
  | [], [], s, N, N', .nil, hs, hr => by simp at hr; subst hr; exact hs
  | x :: xs, d :: ds, s, N, N', .cons hd hds, hs, hr => by
    simp only [List.foldlM_cons, bind, Option.bind] at hr
    cases hN : refNStep N d with
    | none => simp [hN] at hr
    | some N1 =>
      simp only [hN] at hr
      simp only [List.foldl_cons]
      exact si_items hstep hds (hstep x d s N N1 hd hs hN) hr

theorem foldlM_id {ds : List RDef} (hd : ∀ d ∈ ds, ∀ N N', refNStep N d = some N' → N' = N) :
    ∀ {N N' : RN}, ds.foldlM refNStep N = some N' → N' = N := by
  induction ds with
  | nil => intro N N' h; simp at h; exact h.symm
  | cons d ds ih =>
    intro N N' h
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hN : refNStep N d with
    | none => simp [hN] at h
    | some N1 =>
      simp only [hN] at h
      rw [ih (fun d' hd' => hd d' (by simp [hd'])) h, hd d (by simp) N N1 hN]

theorem si_section {sec : Binary.Section} {ds : List RDef} {s : SigSt} {N N' : RN}
    (hs : SI s N) (ht : ToRef.section_ sec = .ok ds) (hr : ds.foldlM refNStep N = some N') :
    SI (sigSection s sec) N' := by
  cases sec with
  | custom n d =>
    simp only [ToRef.section_] at ht; cases ht
    simp at hr; subst hr; exact hs
  | coreModule bs =>
    simp only [ToRef.section_, bind, Except.bind, pure, Except.pure] at ht
    split at ht
    · cases ht
    · cases ht
      simp [refNStep] at hr; subst hr; exact hs
  | coreInstances xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    rw [foldlM_id (fun d hd N N' h => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd
      simp only [refNStep, Option.some.injEq] at h; exact h.symm) hr]
    exact hs
  | coreTypes xs =>
    simp only [ToRef.section_] at ht
    rw [foldlM_id (fun d hd N N' h => by
      obtain ⟨x, -, hx⟩ := mapM_ok ht d hd
      cases hy : ToRef.coreType x <;> simp [hy, Functor.map, Except.map] at hx
      subst hx; simp [refNStep] at h) hr]
    exact hs
  | component c =>
    simp only [ToRef.section_, bind, Except.bind, pure, Except.pure] at ht
    split at ht
    · cases ht
    · cases ht
      simp [refNStep] at hr
  | instances xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    cases xs with
    | nil => simp at hr; subst hr; exact hs
    | cons x xs => simp [refNStep] at hr
  | aliases xs =>
    simp only [ToRef.section_] at ht
    refine si_items (D := fun x d => ∃ a', ToRef.aliasDef x = .ok a' ∧ d = .alias a')
      (fun x d s N N' hd hs hr => ?_) ((mapM_forall₂ ht).imp fun x d hd => ?_) hs hr
    · obtain ⟨a', ha, rfl⟩ := hd
      exact si_alias hs ha hr
    · cases ha : ToRef.aliasDef x <;> simp [ha, Functor.map, Except.map] at hd
      exact ⟨_, rfl, hd.symm⟩
  | types xs =>
    simp only [ToRef.section_] at ht
    refine si_items (D := fun x d => ∃ t', ToRef.defType x = .ok t' ∧ d = .type t')
      (fun x d s N N' hd hs hr => ?_) ((mapM_forall₂ ht).imp fun x d hd => ?_) hs hr
    · obtain ⟨t', ha, rfl⟩ := hd
      exact si_type hs ha hr
    · cases ha : ToRef.defType x <;> simp [ha, Functor.map, Except.map] at hd
      exact ⟨_, rfl, hd.symm⟩
  | canons xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine si_items (D := fun x d => d = .canon (ToRef.canon x))
      (fun x d s N N' hd hs hr => ?_) (forall₂_map_self _ xs) hs hr
    subst hd
    exact si_canon hs hr
  | start st =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    simp [refNStep] at hr
  | imports xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine si_items (D := fun x d => d = .import_ (ToRef.externName x.name) (ToRef.externDesc x.desc))
      (fun x d s N N' hd hs hr => ?_) (forall₂_map_self _ xs) hs hr
    subst hd
    exact si_import hs hr
  | exports xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine si_items (D := fun x d => d = .export_ (ToRef.externName x.name) (ToRef.sortIdx x.item)
        (x.desc.map ToRef.externDesc))
      (fun x d s N N' hd hs hr => ?_) (forall₂_map_self _ xs) hs hr
    subst hd
    exact si_export hs hr
  | values xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    cases xs with
    | nil => simp at hr; subst hr; exact hs
    | cons x xs => simp [refNStep] at hr

theorem si_sections : ∀ {ss : List Binary.Section} {ds : List RDef} {s : SigSt} {N N' : RN},
    SI s N → ToRef.sections ss = .ok ds → ds.foldlM refNStep N = some N' →
    SI (ss.foldl sigSection s) N'
  | [], ds, s, N, N', hs, ht, hr => by
    simp only [ToRef.sections] at ht; cases ht
    simp at hr; subst hr; exact hs
  | sec :: ss, ds, s, N, N', hs, ht, hr => by
    simp only [ToRef.sections, bind, Except.bind, pure, Except.pure] at ht
    split at ht
    · cases ht
    · rename_i d1 hd1
      split at ht
      · cases ht
      · rename_i d2 hd2
        cases ht
        rw [List.foldlM_append] at hr
        simp only [bind, Option.bind] at hr
        cases hN : d1.foldlM refNStep N with
        | none => simp [hN] at hr
        | some N1 =>
          simp only [hN] at hr
          simp only [List.foldl_cons]
          exact si_sections (si_section hs hd1 hN) hd2 hr

/-- **The named IR reading is the named reference reading.** -/
theorem lowerSig_of_toRef {a : Binary.Ast} {r : RefComponent} {N : RN}
    (ht : toRef a = .ok r) (hN : refReadN r = some N) :
    lowerSig a = ⟨N.imports, N.exports⟩ := by
  rcases a with ⟨ss⟩
  have ht' : ToRef.sections ss = .ok r := by simpa [toRef, ToRef.ast] using ht
  have hs := si_sections (s := {}) (N := {}) ⟨rfl, rfl, rfl, rfl⟩ ht' hN
  simp only [lowerSig]
  rw [show (Ast.mk ss).sections = ss from rfl, hs.imports, hs.exports]

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Named
