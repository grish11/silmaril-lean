module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.Sig

/-!
# Export names without exported instances

`exportNames_of_toRef`: for every AST `a` with `Conformance.toRef a = .ok r`, if no definition of
`r` exports an instance (`NoInstExport r`), the export names of the named IR signature
`Binary.Lower.lowerSig a` are the function export names of `r` (`refFuncExportNames r`), in
order. Only `export` definitions add exports on either side: a function export adds its name to
both, a type export (or any other sort but instances) to neither.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Named

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Proofs.Wasm.Component.DecoderBridge (sort_func mapM_ok)

/-- A definition that does not export an instance. -/
def NotInst (d : RDef) : Prop := ∀ n i e, d ≠ .export_ n ⟨.instance_, i⟩ e

theorem notInst_of_noInstExport {r : RefComponent} (h : NoInstExport r) : ∀ d ∈ r, NotInst d := by
  intro d hd n i e he
  subst he
  have := List.all_eq_true.1 h _ hd
  simp at this

theorem foldl_exports {α : Type} {g : SigSt → α → SigSt} (hg : ∀ s x, (g s x).exports = s.exports) :
    ∀ (xs : List α) (s : SigSt), (xs.foldl g s).exports = s.exports
  | [], s => rfl
  | x :: xs, s => by simp only [List.foldl_cons]; rw [foldl_exports hg xs, hg]

theorem sigType_exports (s : SigSt) (t : DefType) : (sigType s t).exports = s.exports := rfl

theorem sigImport_exports (s : SigSt) (i : Import) : (sigImport s i).exports = s.exports := by
  unfold sigImport
  split
  · rfl
  · split <;> rfl
  all_goals rfl

theorem sigAlias_exports (s : SigSt) (a : Alias) : (sigAlias s a).exports = s.exports := by
  unfold sigAlias
  split <;> rfl

theorem sigCanon_exports (s : SigSt) (c : Canon) : (sigCanon s c).exports = s.exports := by
  cases c <;> rfl

theorem sigInstance_exports (s : SigSt) (e : InstanceExpr) : (sigInstance s e).exports = s.exports := by
  cases e <;> rfl

theorem names_nil {ds : List RDef} (h : ∀ d ∈ ds, ∀ n si e, d ≠ .export_ n si e) :
    refFuncExportNames ds = [] := by
  unfold refFuncExportNames
  rw [List.filterMap_eq_nil_iff]
  intro d hd
  split
  · rename_i n i e
    exact absurd rfl (h _ hd n _ e)
  · rfl

theorem sigExport_names (s : SigSt) (x : Binary.Export) (hx : ToRef.sort x.item.sort ≠ .instance_) :
    (sigExport s x).exports.map (·.1) = s.exports.map (·.1) ++
      refFuncExportNames [.export_ (ToRef.externName x.name) (ToRef.sortIdx x.item)
        (x.desc.map ToRef.externDesc)] := by
  rcases x with ⟨n, ⟨srt, i⟩, d⟩
  simp only at hx
  cases srt with
  | func => simp [sigExport, refFuncExportNames, ToRef.sortIdx, ToRef.sort, ToRef.externName]
  | «instance» => exact absurd rfl hx
  | core c => simp [sigExport, refFuncExportNames, ToRef.sortIdx, ToRef.sort]
  | value => simp [sigExport, refFuncExportNames, ToRef.sortIdx, ToRef.sort]
  | type => simp [sigExport, refFuncExportNames, ToRef.sortIdx, ToRef.sort]
  | component => simp [sigExport, refFuncExportNames, ToRef.sortIdx, ToRef.sort]

theorem refFuncExportNames_append (ds ds' : List RDef) :
    refFuncExportNames (ds ++ ds') = refFuncExportNames ds ++ refFuncExportNames ds' := by
  simp [refFuncExportNames, List.filterMap_append]

theorem refFuncExportNames_cons (d : RDef) (ds : List RDef) :
    refFuncExportNames (d :: ds) = refFuncExportNames [d] ++ refFuncExportNames ds := by
  rw [← refFuncExportNames_append]; rfl

theorem exports_names : ∀ (xs : List Binary.Export) (s : SigSt),
    (∀ x ∈ xs, ToRef.sort x.item.sort ≠ .instance_) →
    (xs.foldl sigExport s).exports.map (·.1) = s.exports.map (·.1) ++
      refFuncExportNames (xs.map fun x =>
        .export_ (ToRef.externName x.name) (ToRef.sortIdx x.item) (x.desc.map ToRef.externDesc))
  | [], s, _ => by simp [refFuncExportNames]
  | x :: xs, s, h => by
    simp only [List.foldl_cons, List.map_cons]
    rw [exports_names xs _ (fun y hy => h y (by simp [hy])),
      sigExport_names s x (h x (by simp)), List.append_assoc]
    conv_rhs => rw [refFuncExportNames_cons]

theorem section_names {sec : Binary.Section} {ds : List RDef} (s : SigSt)
    (ht : ToRef.section_ sec = .ok ds) (hn : ∀ d ∈ ds, NotInst d) :
    (sigSection s sec).exports.map (·.1) = s.exports.map (·.1) ++ refFuncExportNames ds := by
  cases sec with
  | exports xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine exports_names xs s (fun x hx hs => ?_)
    rcases x with ⟨n, ⟨srt, i⟩, e⟩
    exact hn _ (List.mem_map.2 ⟨_, hx, rfl⟩) _ i _ (by simp only [ToRef.sortIdx] at hs ⊢; rw [hs])
  | _ =>
    rw [names_nil, List.append_nil]
    · first
        | rfl
        | (simp only [sigSection]
           first
             | exact congrArg _ (foldl_exports sigType_exports _ _)
             | exact congrArg _ (foldl_exports sigImport_exports _ _)
             | exact congrArg _ (foldl_exports sigAlias_exports _ _)
             | exact congrArg _ (foldl_exports sigCanon_exports _ _)
             | exact congrArg _ (foldl_exports sigInstance_exports _ _))
    · intro d hd n si e he
      subst he
      first
        | (simp only [ToRef.section_, Except.ok.injEq] at ht; subst ht
           first
             | (obtain ⟨x, -, hx⟩ := List.mem_map.1 hd; cases hx)
             | simp at hd)
        | (simp only [ToRef.section_] at ht
           obtain ⟨x, -, hx⟩ := mapM_ok ht _ hd
           first
             | (cases hy : ToRef.coreType x <;> simp [hy, Functor.map, Except.map] at hx)
             | (cases hy : ToRef.aliasDef x <;> simp [hy, Functor.map, Except.map] at hx)
             | (cases hy : ToRef.defType x <;> simp [hy, Functor.map, Except.map] at hx))
        | (simp only [ToRef.section_, bind, Except.bind, pure, Except.pure] at ht
           split at ht
           · cases ht
           · cases ht; simp at hd)

theorem sections_names : ∀ {ss : List Binary.Section} {ds : List RDef} (s : SigSt),
    ToRef.sections ss = .ok ds → (∀ d ∈ ds, NotInst d) →
    (ss.foldl sigSection s).exports.map (·.1) = s.exports.map (·.1) ++ refFuncExportNames ds
  | [], ds, s, ht, _ => by
    simp only [ToRef.sections] at ht; cases ht; simp [refFuncExportNames]
  | sec :: ss, ds, s, ht, hn => by
    simp only [ToRef.sections, bind, Except.bind, pure, Except.pure] at ht
    split at ht
    · cases ht
    · rename_i d1 hd1
      split at ht
      · cases ht
      · rename_i d2 hd2
        cases ht
        simp only [List.foldl_cons]
        rw [sections_names _ hd2 (fun d hd => hn d (by simp [hd])),
          section_names s hd1 (fun d hd => hn d (by simp [hd])), refFuncExportNames_append,
          List.append_assoc]

/-- **Without exported instances, the named IR exports the reference's function exports, by
name.** -/
theorem exportNames_of_toRef {a : Binary.Ast} {r : RefComponent} (ht : toRef a = .ok r)
    (hn : NoInstExport r) : (lowerSig a).exports.map (·.1) = refFuncExportNames r := by
  rcases a with ⟨ss⟩
  have ht' : ToRef.sections ss = .ok r := by simpa [toRef, ToRef.ast] using ht
  exact sections_names {} ht' (notInst_of_noInstExport hn)

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Named
