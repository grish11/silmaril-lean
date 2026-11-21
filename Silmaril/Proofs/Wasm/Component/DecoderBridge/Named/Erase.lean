module

public import Silmaril.Wasm.Component.DecoderBridge.Named.Defs

/-!
# The named reading of a reference component erases to the symbolic reading

`refReadN_of_refRead`: if the symbolic reading `refRead r` succeeds (`InFrag r`), so does the
named reading `refReadN r`, and erasing its parameter names gives the symbolic reading's
types, functions, imports and exports (invariant `NR`, one definition at a time).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Named

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge

/-- A reference definition. -/
abbrev RDef := Syntax.Definition Silmaril.Wasm.Module

theorem mapM_length {α β : Type} {g : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM g = some ys → ys.length = xs.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : g x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM g with
      | none => simp [hx, hxs] at h
      | some ys' =>
        simp [hx, hxs] at h; subst h
        simp [mapM_length hxs]

/-- The parameters of a function type of the fragment are as many as its parameter names. -/
theorem refFuncTy_length {f : Syntax.FuncType} {ft : FuncTy} (h : refFuncTy f = some ft) :
    ft.params.length = f.params.length := by
  unfold refFuncTy at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  cases hps : f.params.mapM fun p => refVT p.2 with
  | none => simp [hps] at h
  | some ps =>
    simp only [hps] at h
    have hl := mapM_length hps
    revert h
    cases f.result with
    | none =>
      simp only
      intro h
      split at h
      · cases h
      split at h
      · cases h
      cases h; exact hl
    | some t =>
      simp only
      cases refVT t with
      | none => simp
      | some v =>
        simp only [Option.map_some]
        intro h
        split at h
        · cases h
        split at h
        · cases h
        cases h; exact hl

theorem erase_named {ns : List String} {ft : FuncTy} (h : ft.params.length = ns.length) :
    (⟨ns.zip ft.params, ft.results⟩ : NFuncTy).erase = ft := by
  rcases ft with ⟨ps, rs⟩
  simp only [NFuncTy.erase]
  congr
  exact List.map_snd_zip (by simp at h; omega)

theorem refNFuncTy_of {f : Syntax.FuncType} {ft : FuncTy} (h : refFuncTy f = some ft) :
    ∃ nf, refNFuncTy f = some nf ∧ nf.erase = ft :=
  ⟨⟨(f.params.map (·.1)).zip ft.params, ft.results⟩, by simp [refNFuncTy, h],
    erase_named (by simpa using refFuncTy_length h)⟩

/-- **The named reading erases to the symbolic reading.** -/
structure NR (R : RSt) (N : RN) : Prop where
  types : N.types.map NFuncTy.erase = R.types
  funcs : N.funcs.map NFuncTy.erase = R.funcs.map (·.2)
  imports : NIface.erase N.imports = R.imports
  exports : N.exports.map (fun p => (p.1, p.2.erase)) = R.exports.map fun e => (e.name, e.ty)

theorem getElem?_erase {xs : List NFuncTy} {ys : List FuncTy} (h : xs.map NFuncTy.erase = ys)
    {i : Nat} {y : FuncTy} (hy : ys[i]? = some y) : ∃ x, xs[i]? = some x ∧ x.erase = y := by
  subst h
  rw [List.getElem?_map] at hy
  cases hx : xs[i]? with
  | none => simp [hx] at hy
  | some x => simp [hx] at hy; exact ⟨x, rfl, hy⟩

theorem getElem?_erase2 {xs : List NFuncTy} {ys : List (Impl × FuncTy)}
    (h : xs.map NFuncTy.erase = ys.map (·.2)) {i : Nat} {y : Impl × FuncTy} (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ x.erase = y.2 := by
  have : (ys.map (·.2))[i]? = some y.2 := by simp [hy]
  exact getElem?_erase h this

theorem nr_of_eq {R R' : RSt} {N : RN} (hn : NR R N)
    (h : R'.types = R.types ∧ R'.funcs = R.funcs ∧ R'.imports = R.imports ∧ R'.exports = R.exports) :
    NR R' N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1 ▸ hn.1, h2 ▸ hn.2, h3 ▸ hn.3, h4 ▸ hn.4⟩

theorem nr_step {R R' : RSt} {N : RN} {d : RDef} (hn : NR R N) (h : refStep R d = some R') :
    ∃ N', refNStep N d = some N' ∧ NR R' N' := by
  unfold refStep at h
  split at h
  · cases h; exact ⟨N, rfl, ⟨hn.1, hn.2, hn.3, hn.4⟩⟩
  · rename_i f
    simp only [bind, Option.bind] at h
    cases hf : refFuncTy f with
    | none => simp [hf] at h
    | some ft =>
      simp only [hf, Option.some.injEq] at h; subst h
      obtain ⟨nf, hnf, he⟩ := refNFuncTy_of hf
      exact ⟨{ N with types := N.types ++ [nf] }, by simp [refNStep, hnf],
        { hn with types := by simp [hn.types, he] }⟩
  · rename_i n t
    simp only [bind, Option.bind] at h
    cases ht : R.types[t]? with
    | none => simp [ht] at h
    | some ft =>
      simp only [ht, Option.some.injEq] at h; subst h
      obtain ⟨nf, hnf, he⟩ := getElem?_erase hn.types ht
      exact ⟨{ N with funcs := N.funcs ++ [nf], imports := N.imports ++ [(n.name, nf)] },
        by simp [refNStep, hnf],
        { hn with
          funcs := by simp [hn.funcs, he]
          imports := by simp [NIface.erase, ← hn.imports, he] }⟩
  · exact ⟨N, rfl, nr_of_eq hn (by simp only [bind, Option.bind_eq_some_iff] at h; aesop)⟩
  · exact ⟨N, rfl, nr_of_eq hn (by simp only [bind, Option.bind_eq_some_iff] at h; aesop)⟩
  · exact ⟨N, rfl, nr_of_eq hn (by simp only [bind, Option.bind_eq_some_iff] at h; aesop)⟩
  · rename_i f t
    simp only [bind, Option.bind] at h
    split at h
    · cases h
    rename_i im him
    cases ht : R.types[t]? with
    | none => simp [ht] at h
    | some ft =>
      simp only [ht, Option.some.injEq] at h; subst h
      obtain ⟨nf, hnf, he⟩ := getElem?_erase hn.types ht
      exact ⟨{ N with funcs := N.funcs ++ [nf] }, by simp [refNStep, hnf],
        { hn with funcs := by simp [hn.funcs, he] }⟩
  · exact ⟨N, rfl, nr_of_eq hn (by
      simp only [bind, Option.bind_eq_some_iff, ne_eq, ite_not] at h
      obtain ⟨p, -, h⟩ := h
      split at h
      · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
      · cases h)⟩
  · rename_i n i
    simp only [bind, Option.bind] at h
    cases hf : R.funcs[i]? with
    | none => simp [hf] at h
    | some p =>
      simp only [hf, Option.some.injEq] at h; subst h
      obtain ⟨nf, hnf, he⟩ := getElem?_erase2 hn.funcs hf
      exact ⟨{ N with exports := N.exports ++ [(n.name, nf)], funcs := N.funcs ++ [nf] },
        by simp [refNStep, hnf],
        { hn with
          funcs := by simp [hn.funcs, he]
          exports := by simp [hn.exports, he] }⟩
  · cases h

theorem nr_foldlM : ∀ {ds : List RDef} {R R' : RSt} {N : RN}, NR R N →
    ds.foldlM refStep R = some R' → ∃ N', ds.foldlM refNStep N = some N' ∧ NR R' N'
  | [], R, R', N, hn, h => by simp at h; subst h; exact ⟨N, rfl, hn⟩
  | d :: ds, R, R', N, hn, h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      obtain ⟨N1, h1, hn1⟩ := nr_step hn hR
      obtain ⟨N', h2, hn'⟩ := nr_foldlM hn1 h
      exact ⟨N', by simp [List.foldlM_cons, h1, h2], hn'⟩

/-- **On the fragment the named reading succeeds and erases to the symbolic reading.** -/
theorem refReadN_of_refRead {r : RefComponent} {R : RSt} (h : refRead r = some R) :
    ∃ N, refReadN r = some N ∧ NR R N :=
  nr_foldlM ⟨rfl, rfl, rfl, rfl⟩ h

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Named
