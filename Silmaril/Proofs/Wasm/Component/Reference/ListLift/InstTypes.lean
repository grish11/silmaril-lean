module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.InstCore

/-!
# Instantiating the type definitions of `ListComp.toRef`

The type definitions `ListComp.typeDefs` (one `(type (list …))` per list type, then the function
type of each export) run without a machine operation (`PureTys`). The value type emitted for a
parameter type `t` resolves to `t.toClosed` (`LTy.emit_run`), and the function type emitted for
export `x`, at index `funcTypeIdx`, resolves to `liftedFtL x` (`typeDefs_run`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)

/-! ## Equations of the emitters -/

section Emit

theorem LTy.emit_list {M : Type} (t : LTy) (n : Nat) :
    LTy.emit (M := M) (.list t) n =
      (.idx (t.emit (M := M) n).2.2,
        (t.emit (M := M) n).2.1 ++ [.type (.val (.list (t.emit (M := M) n).1))],
        (t.emit (M := M) n).2.2 + 1) := by
  simp only [LTy.emit]

/-- The emitted value type and the next index do not depend on the module type. -/
theorem LTy.emit_fst_snd {M M' : Type} : ∀ (t : LTy) (n : Nat),
    (t.emit (M := M) n).1 = (t.emit (M := M') n).1 ∧
      (t.emit (M := M) n).2.2 = (t.emit (M := M') n).2.2
  | .s32, _ => ⟨rfl, rfl⟩
  | .list t, n => by
    rw [LTy.emit_list, LTy.emit_list (M := M')]
    obtain ⟨h₁, h₂⟩ := LTy.emit_fst_snd (M := M) (M' := M') t n
    exact ⟨by rw [h₂], by rw [h₂]⟩

theorem emitParams_cons {M : Type} (x : String) (t : LTy) (ps : List (String × LTy)) (n : Nat) :
    emitParams (M := M) ((x, t) :: ps) n =
      ((x, (t.emit (M := M) n).1) :: (emitParams (M := M) ps (t.emit (M := M) n).2.2).1,
        (t.emit (M := M) n).2.1 ++ (emitParams (M := M) ps (t.emit (M := M) n).2.2).2.1,
        (emitParams (M := M) ps (t.emit (M := M) n).2.2).2.2) := by
  simp only [emitParams]

/-- The next index after the parameters does not depend on the module type. -/
theorem emitParams_snd {M M' : Type} : ∀ (ps : List (String × LTy)) (n : Nat),
    (emitParams (M := M) ps n).2.2 = (emitParams (M := M') ps n).2.2
  | [], _ => rfl
  | (x, t) :: ps, n => by
    rw [emitParams_cons, emitParams_cons (M := M'), (LTy.emit_fst_snd (M := M) (M' := M') t n).2]
    exact emitParams_snd ps _

theorem typeDefs_cons {M : Type} (x : ListExport) (xs : List ListExport) (n : Nat) :
    ListComp.typeDefs (M := M) (x :: xs) n =
      (emitParams (M := M) x.params n).2.1 ++
        [.type (.func { params := (emitParams (M := M) x.params n).1,
                        result := some (.prim .bool) })] ++
        ListComp.typeDefs (M := M) xs ((emitParams (M := M) x.params n).2.2 + 1) := by
  simp only [ListComp.typeDefs]

theorem funcTypeIdx_cons (x : ListExport) (xs : List ListExport) (n : Nat) :
    ListComp.funcTypeIdx (x :: xs) n =
      (emitParams (M := Silmaril.Wasm.Module) x.params n).2.2 ::
        ListComp.funcTypeIdx xs ((emitParams (M := Silmaril.Wasm.Module) x.params n).2.2 + 1) := by
  simp only [ListComp.funcTypeIdx]

end Emit

/-! ## Runs of the emitted definitions -/

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]
  {R : Recurse E σ} {inst : InstId} {outer : List (Frame E)} {args : Exports E}

/-- **The definitions emitted for a parameter type run without a machine operation** and the
emitted value type resolves to `t.toClosed`. -/
theorem LTy.emit_run : ∀ (t : LTy) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc (t.emit (M := E.Module) sc.frame.types.length).2.1 sc'
        (t.emit (M := E.Module) sc.frame.types.length).2.2 ∧
      Res sc'.frame.types (t.emit (M := E.Module) sc.frame.types.length).1 t.toClosed
  | .s32, sc => ⟨sc, PureTys.nil sc, Res.prim _ .s32⟩
  | .list t, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := LTy.emit_run t sc
    have hl₁ : sc₁.frame.types.length = (t.emit (M := E.Module) sc.frame.types.length).2.2 :=
      hP₁.2.2.1
    have hres : resolveDefValType? sc₁.frame
        (.list (t.emit (M := E.Module) sc.frame.types.length).1) = some (.list t.toClosed) := by
      simp only [resolveDefValType?, hR₁ sc₁.frame (List.prefix_refl _), Option.map_eq_map,
        Option.map_some]
    have hP₂ := PureTys.val (R := R) (inst := inst) (outer := outer) (args := args) sc₁ hres
    rw [LTy.emit_list, ← hl₁]
    refine ⟨_, hP₁.trans hP₂, Res.idx ?_⟩
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]
    rfl

/-- `LTy.emit_run` on named parameters. -/
theorem emitParams_run : ∀ (ps : List (String × LTy)) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc (emitParams (M := E.Module) ps sc.frame.types.length).2.1
        sc' (emitParams (M := E.Module) ps sc.frame.types.length).2.2 ∧
      List.Forall₂ (fun (a : String × Syntax.VT) (b : String × LTy) =>
          a.1 = b.1 ∧ Res sc'.frame.types a.2 b.2.toClosed)
        (emitParams (M := E.Module) ps sc.frame.types.length).1 ps
  | [], sc => ⟨sc, PureTys.nil sc, .nil⟩
  | (x, t) :: ps, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := LTy.emit_run (R := R) (inst := inst) (outer := outer)
      (args := args) t sc
    obtain ⟨sc₂, hP₂, hR₂⟩ := emitParams_run ps sc₁
    have hl₁ : sc₁.frame.types.length = (t.emit (M := E.Module) sc.frame.types.length).2.2 :=
      hP₁.2.2.1
    rw [emitParams_cons, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, .cons ⟨rfl, hR₁.mono hP₂.prefix⟩ hR₂⟩

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The resolved parameters of an emitted function type. -/
theorem mapM_params {f : Frame E} :
    ∀ {vs : List (String × Syntax.VT)} {ps : List (String × LTy)},
      List.Forall₂ (fun (a : String × Syntax.VT) (b : String × LTy) =>
          a.1 = b.1 ∧ Res f.types a.2 b.2.toClosed) vs ps →
      vs.mapM (fun (p : String × Syntax.VT) => (p.1, ·) <$> resolveValType? f p.2) =
        some (ps.map fun p => (p.1, p.2.toClosed))
  | [], [], .nil => rfl
  | (n, v) :: vs, (n', t) :: ps, .cons ⟨hn, hr⟩ hs => by
    have hn' : n = n' := hn
    subst hn'
    rw [List.mapM_cons, mapM_params hs, hr f (List.prefix_refl _), List.map_cons]
    rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The emitted function type of an export resolves to its lifted function type. -/
theorem resolveFuncType_liftedL {f : Frame E} {x : ListExport} {vs : List (String × Syntax.VT)}
    (h : List.Forall₂ (fun (a : String × Syntax.VT) (b : String × LTy) =>
        a.1 = b.1 ∧ Res f.types a.2 b.2.toClosed) vs x.params) :
    resolveFuncType? f { params := vs, result := some (.prim .bool) } = some (liftedFtL x) := by
  have hm := mapM_params h
  simp only [resolveFuncType?] at hm ⊢
  rw [hm]
  rfl

/-- **The type definitions of the exports run without a machine operation**, and the function
type of each export, at its index `funcTypeIdx`, resolves to its lifted function type. -/
theorem typeDefs_run : ∀ (xs : List ListExport) (sc : Scope E),
    ∃ sc' n', PureTys R inst outer args sc
        (ListComp.typeDefs (M := E.Module) xs sc.frame.types.length) sc' n' ∧
      List.Forall₂ (fun t x => sc'.frame.types[t]? = some (.func (liftedFtL x)))
        (ListComp.funcTypeIdx xs sc.frame.types.length) xs
  | [], sc => ⟨sc, _, PureTys.nil sc, .nil⟩
  | x :: xs, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := emitParams_run (R := R) (inst := inst) (outer := outer)
      (args := args) x.params sc
    have hl₁ : sc₁.frame.types.length =
        (emitParams (M := E.Module) x.params sc.frame.types.length).2.2 := hP₁.2.2.1
    have hft := resolveFuncType_liftedL (f := sc₁.frame) (x := x)
      (hR₁.imp fun _ _ h => ⟨h.1, h.2⟩)
    have hP₂ : PureTys R inst outer args sc₁
        [.type (.func { params := (emitParams (M := E.Module) x.params sc.frame.types.length).1,
                        result := some (.prim .bool) })]
        { sc₁ with frame := { sc₁.frame with types := sc₁.frame.types ++ [.func (liftedFtL x)] } }
        (sc₁.frame.types.length + 1) :=
      ⟨foldlM_single (instDef_func sc₁ hft), ⟨_, rfl⟩, List.length_append, rfl,
        fun _ hd => by rw [List.mem_singleton.1 hd]; intro _ _ e; cases e⟩
    obtain ⟨sc₃, n₃, hP₃, hR₃⟩ := typeDefs_run xs
      { sc₁ with frame := { sc₁.frame with types := sc₁.frame.types ++ [.func (liftedFtL x)] } }
    have hl₂ : (sc₁.frame.types ++ [Types.TypeDef.func (liftedFtL x)]).length =
        (emitParams (M := E.Module) x.params sc.frame.types.length).2.2 + 1 := by
      rw [List.length_append, hl₁]
      rfl
    rw [hl₂] at hP₃ hR₃
    rw [typeDefs_cons, funcTypeIdx_cons,
      ← emitParams_snd (M := E.Module) (M' := Silmaril.Wasm.Module)]
    refine ⟨sc₃, n₃, (hP₁.trans hP₂).trans hP₃, .cons ?_ hR₃⟩
    obtain ⟨l, hl⟩ := hP₃.prefix
    have hx : (sc₁.frame.types ++ [Types.TypeDef.func (liftedFtL x)])[sc₁.frame.types.length]? =
        some (.func (liftedFtL x)) := by simp
    rw [← hl₁, ← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]
    exact hx

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
