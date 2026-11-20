module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.Erase
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Root

/-!
# The named imports decide the root checks

`rootChecked_of_refReadN`: if the named reading of a reference component succeeds and its
imports are `hostIN` (`f: func(x: u32)`, parameter name included), the component passes the
reference machine's root checks (`RootChecked`):

* `argsComplete`: every import definition is a function import the named reading lists, so its
  name is `f`, which the host supplies;
* `precheckImports`: the walk of the pre-check follows the named reading definition by
  definition (invariant `PInv`: the frame's types are as many as the reading's, and where the
  reading has `func(x: u32)` the frame has its resolution `tX`); at the import `f` of type `t`
  the reading's type is `hostFN`, so the frame's is `tX`, and the import check is the closed
  computation `Multi.check_pre`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Named

open Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.SingleThreaded (neverFail)

theorem refVT_u32 {p : Syntax.VT} (h : refVT p = some .u32) : p = .prim .u32 := by
  cases p with
  | prim q => cases q <;> simp [refVT, refPrim] at h ⊢
  | idx i => simp [refVT] at h

/-- **Only `func(x: u32)` reads as `hostFN`.** -/
theorem refNFuncTy_hostFN {f : Syntax.FuncType} (h : refNFuncTy f = some hostFN) :
    f = fFuncType := by
  rcases f with ⟨asy, ps, res⟩
  simp only [refNFuncTy, Option.map_eq_some_iff] at h
  obtain ⟨ft, hft, he⟩ := h
  have hl := refFuncTy_length hft
  simp only [hostFN, NFuncTy.mk.injEq] at he
  obtain ⟨hz, hr⟩ := he
  simp only at hl
  match ps, hz, hl with
  | [(x, p)], hz, hl =>
    obtain ⟨v, hv⟩ : ∃ v, ft.params = [v] := by
      match hp : ft.params, hl with
      | [v], _ => exact ⟨v, rfl⟩
    rw [hv] at hz
    simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right,
      List.cons.injEq, Prod.mk.injEq, and_true] at hz
    obtain ⟨rfl, rfl⟩ := hz
    cases asy with
    | true => simp [refFuncTy] at hft
    | false =>
      cases hp : refVT p with
      | none => simp [refFuncTy, hp] at hft
      | some w =>
        cases res with
        | none =>
          simp only [refFuncTy, hp, Bool.false_eq_true, ite_false, bind, Option.bind,
            List.mapM_cons, List.mapM_nil] at hft
          simp at hft
          obtain ⟨-, -, rfl⟩ := hft
          simp only [List.cons.injEq, and_true] at hv
          subst hv
          rw [refVT_u32 hp]
          rfl
        | some t =>
          cases ht : refVT t with
          | none => simp [refFuncTy, hp, ht] at hft
          | some u =>
            simp only [refFuncTy, hp, ht, Bool.false_eq_true, ite_false, bind, Option.bind,
              List.mapM_cons, List.mapM_nil] at hft
            simp at hft
            obtain ⟨-, -, rfl⟩ := hft
            simp at hr
  | [], hz, hl =>
    cases hp : ft.params with
    | nil => rw [hp] at hz; simp at hz
    | cons _ _ => rw [hp] at hl; simp at hl
  | _ :: _ :: _, hz, hl =>
    match hp : ft.params, hl with
    | _ :: _ :: _, _ =>
      rw [hp] at hz; simp at hz

/-! ## The pre-check walk -/

/-- The walk's invariant. -/
def PInv (f : Frame (core3 neverFail)) (N : RN) : Prop :=
  f.types.length = N.types.length ∧ ∀ i : Nat, N.types[i]? = some hostFN → f.types[i]? = some (Types.TypeDef.func tX)

theorem pinv_empty : PInv Frame.empty ({} : RN) := ⟨rfl, fun i h => by simp at h⟩

theorem imports_prefix : ∀ {ds : List RDef} {N N' : RN}, ds.foldlM refNStep N = some N' →
    N.imports <+: N'.imports
  | [], N, N', h => by simp at h; subst h; exact List.prefix_refl _
  | d :: ds, N, N', h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hN : refNStep N d with
    | none => simp [hN] at h
    | some N1 =>
      simp only [hN] at h
      refine List.IsPrefix.trans ?_ (imports_prefix h)
      unfold refNStep at hN
      split at hN
      all_goals first
        | (simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hN
           obtain ⟨_, -, rfl⟩ := hN
           first | exact List.prefix_append _ _ | exact List.prefix_refl _)
        | cases hN

theorem funcTypeAt_of {f : Frame (core3 neverFail)} {t : Nat} (h : f.types[t]? = some (Types.TypeDef.func tX)) :
    funcTypeAt? f t = some tX := by
  simp [funcTypeAt?, Frame.type?, h]

theorem importTypeCheck_f {s : CStore (core3 neverFail)} {f : Frame (core3 neverFail)} {t : Nat}
    (h : f.types[t]? = some (Types.TypeDef.func tX)) (v : ItemVal (core3 neverFail)) :
    importTypeCheck s f "f" (.func t) v = importTypeCheck s frameT "f" (.func 0) v := by
  have h0 : funcTypeAt? frameT 0 = some tX := rfl
  simp only [importTypeCheck, descEntity?, funcTypeAt_of h, h0]

theorem resolve_fFuncType' (f : Frame (core3 neverFail)) : resolveFuncType? f fFuncType = some tX :=
  rfl

/-- **The pre-check walk passes.** -/
theorem precheck_walk : ∀ {ds : List RDef} {f : Frame (core3 neverFail)} {N N' : RN}, PInv f N →
    ds.foldlM refNStep N = some N' → (∀ x ∈ N'.imports, x = ("f", hostFN)) →
    precheckImports preStore (importArgs hostI) f ds = .ok ()
  | [], f, N, N', _, _, _ => rfl
  | d :: ds, f, N, N', hi, h, himp => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hN : refNStep N d with
    | none => simp [hN] at h
    | some N1 =>
      simp only [hN] at h
      have hpre := imports_prefix h
      have ih := fun f (hi : PInv f N1) => precheck_walk hi h himp
      unfold refNStep at hN
      split at hN
      · cases hN; exact ih f hi
      · rename_i sf
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hN
        obtain ⟨nf, hnf, rfl⟩ := hN
        simp only [precheckImports, precheckDef]
        cases hst : staticType? f [] (.func sf) with
        | none => rfl
        | some ty =>
          simp only [Option.bind_some, Frame.push]
          refine ih _ ⟨by simp [hi.1], fun i hix => ?_⟩
          simp only at hix ⊢
          by_cases hlt : i < N.types.length
          · rw [List.getElem?_append_left hlt] at hix
            rw [List.getElem?_append_left (hi.1 ▸ hlt)]
            exact hi.2 i hix
          · have hge : N.types.length ≤ i := Nat.le_of_not_lt hlt
            rw [List.getElem?_append_right hge] at hix
            rw [List.getElem?_append_right (hi.1 ▸ hge), hi.1]
            cases hk : i - N.types.length with
            | zero =>
              rw [hk] at hix
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hix ⊢
              subst hix
              have := refNFuncTy_hostFN hnf
              subst this
              simp only [staticType?, resolve_fFuncType', Option.map_some, Option.some.injEq] at hst
              rw [← hst]
            | succ k => rw [hk] at hix; simp at hix
      · rename_i n t
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hN
        obtain ⟨ft, hft, rfl⟩ := hN
        have hx : (n.name, ft) = ("f", hostFN) :=
          himp _ (hpre.subset (by simp))
        simp only [Prod.mk.injEq] at hx
        obtain ⟨hn, rfl⟩ := hx
        have hty := hi.2 t hft
        simp only [precheckImports, precheckDef, hn, lookup_f]
        rw [importTypeCheck_f hty, check_pre]
        exact ih f ⟨hi.1, hi.2⟩
      · cases hN; simp only [precheckImports, precheckDef]; exact ih f hi
      · cases hN; simp only [precheckImports, precheckDef]; exact ih f hi
      · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hN
        obtain ⟨ft, -, rfl⟩ := hN
        simp only [precheckImports, precheckDef]; exact ih f ⟨hi.1, hi.2⟩
      · cases hN; simp only [precheckImports, precheckDef]; exact ih f hi
      · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hN
        obtain ⟨ft, -, rfl⟩ := hN
        simp only [precheckImports, precheckDef, typeRelevant]
        exact ih f ⟨hi.1, hi.2⟩
      · cases hN

/-- Every import name is the name of an import of the named reading. -/
theorem importNames_sub : ∀ {ds : List RDef} {N N' : RN}, ds.foldlM refNStep N = some N' →
    ∀ x ∈ importNames ds, x ∈ N'.imports.map (·.1)
  | [], N, N', _, x, hx => by simp [importNames] at hx
  | d :: ds, N, N', h, x, hx => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hN : refNStep N d with
    | none => simp [hN] at h
    | some N1 =>
      simp only [hN] at h
      have hpre := imports_prefix h
      cases d with
      | import_ n e =>
        simp only [importNames, List.filterMap_cons] at hx
        rcases List.mem_cons.1 hx with rfl | hx
        · cases e with
          | func t =>
            simp only [refNStep, bind, Option.bind_eq_some_iff, Option.some.injEq] at hN
            obtain ⟨ft, -, rfl⟩ := hN
            exact List.mem_map.2 ⟨(n.name, ft), hpre.subset (by simp), rfl⟩
          | _ => simp [refNStep] at hN
        · exact importNames_sub h x hx
      | _ =>
        simp only [importNames, List.filterMap_cons] at hx
        exact importNames_sub h x hx

/-- **The named imports `hostIN` decide the root checks.** -/
theorem rootChecked_of_refReadN {r : RefComponent} {N : RN} (h : refReadN r = some N)
    (hi : N.imports = hostIN) : RootChecked r := by
  have himp : ∀ x ∈ N.imports, x = ("f", hostFN) := by
    rw [hi]; intro x hx; simpa [hostIN] using hx
  unfold RootChecked rootChecked
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold argsComplete
    rw [List.all_eq_true]
    intro x hx
    have := importNames_sub h x hx
    rw [hi] at this
    simp only [hostIN, List.map_cons, List.map_nil, List.mem_singleton] at this
    subst this
    rfl
  · show (precheckImports preStore (importArgs hostI) Frame.empty r).toBool = true
    rw [precheck_walk pinv_empty h himp]
    rfl

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Named
