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

theorem LTy.emit_tuple {M : Type} (t : LTy) (ts : List LTy) (n : Nat) :
    LTy.emit (M := M) (.tuple t ts) n =
      (.idx (LTy.emitList (M := M) (t :: ts) n).2.2,
        (LTy.emitList (M := M) (t :: ts) n).2.1 ++
          [.type (.val (.tuple (LTy.emitList (M := M) (t :: ts) n).1))],
        (LTy.emitList (M := M) (t :: ts) n).2.2 + 1) := by
  simp only [LTy.emit, LTy.emitList]

theorem LTy.emit_record {M : Type} (name l : String) (t : LTy) (fs : List (String × LTy))
    (n : Nat) :
    LTy.emit (M := M) (.record name l t fs) n =
      (.idx ((LTy.emitFields (M := M) ((l, t) :: fs) n).2.2 + 1),
        (LTy.emitFields (M := M) ((l, t) :: fs) n).2.1 ++
          [.type (.val (.record (LTy.emitFields (M := M) ((l, t) :: fs) n).1)),
            .export_ { name := name } ⟨.type, (LTy.emitFields (M := M) ((l, t) :: fs) n).2.2⟩
              none],
        (LTy.emitFields (M := M) ((l, t) :: fs) n).2.2 + 2) := by
  simp only [LTy.emit, LTy.emitFields]

theorem LTy.emitList_cons {M : Type} (t : LTy) (ts : List LTy) (n : Nat) :
    LTy.emitList (M := M) (t :: ts) n =
      ((t.emit (M := M) n).1 :: (LTy.emitList (M := M) ts (t.emit (M := M) n).2.2).1,
        (t.emit (M := M) n).2.1 ++ (LTy.emitList (M := M) ts (t.emit (M := M) n).2.2).2.1,
        (LTy.emitList (M := M) ts (t.emit (M := M) n).2.2).2.2) := by
  simp only [LTy.emitList]

theorem LTy.emitFields_cons {M : Type} (l : String) (t : LTy) (fs : List (String × LTy))
    (n : Nat) :
    LTy.emitFields (M := M) ((l, t) :: fs) n =
      ((l, (t.emit (M := M) n).1) :: (LTy.emitFields (M := M) fs (t.emit (M := M) n).2.2).1,
        (t.emit (M := M) n).2.1 ++ (LTy.emitFields (M := M) fs (t.emit (M := M) n).2.2).2.1,
        (LTy.emitFields (M := M) fs (t.emit (M := M) n).2.2).2.2) := by
  simp only [LTy.emitFields]

mutual
/-- The emitted value type and the next index do not depend on the module type. -/
theorem LTy.emit_fst_snd {M M' : Type} : ∀ (t : LTy) (n : Nat),
    (t.emit (M := M) n).1 = (t.emit (M := M') n).1 ∧
      (t.emit (M := M) n).2.2 = (t.emit (M := M') n).2.2
  | .s32, _ => ⟨rfl, rfl⟩
  | .u32, _ => ⟨rfl, rfl⟩
  | .s64, _ => ⟨rfl, rfl⟩
  | .list t, n => by
    rw [LTy.emit_list, LTy.emit_list (M := M')]
    obtain ⟨h₁, h₂⟩ := LTy.emit_fst_snd (M := M) (M' := M') t n
    exact ⟨by rw [h₂], by rw [h₂]⟩
  | .tuple t ts, n => by
    rw [LTy.emit_tuple, LTy.emit_tuple (M := M'), LTy.emitList_cons, LTy.emitList_cons (M := M')]
    obtain ⟨-, h₂⟩ := LTy.emit_fst_snd (M := M) (M' := M') t n
    rw [h₂]
    obtain ⟨-, h₄⟩ := LTy.emitList_fst_snd (M := M) (M' := M') ts (t.emit (M := M') n).2.2
    exact ⟨by rw [h₄], by rw [h₄]⟩
  | .record name l t fs, n => by
    rw [LTy.emit_record, LTy.emit_record (M := M'), LTy.emitFields_cons,
      LTy.emitFields_cons (M := M')]
    obtain ⟨-, h₂⟩ := LTy.emit_fst_snd (M := M) (M' := M') t n
    rw [h₂]
    obtain ⟨-, h₄⟩ := LTy.emitFields_fst_snd (M := M) (M' := M') fs (t.emit (M := M') n).2.2
    exact ⟨by rw [h₄], by rw [h₄]⟩

theorem LTy.emitList_fst_snd {M M' : Type} : ∀ (ts : List LTy) (n : Nat),
    (LTy.emitList (M := M) ts n).1 = (LTy.emitList (M := M') ts n).1 ∧
      (LTy.emitList (M := M) ts n).2.2 = (LTy.emitList (M := M') ts n).2.2
  | [], _ => ⟨rfl, rfl⟩
  | t :: ts, n => by
    rw [LTy.emitList_cons, LTy.emitList_cons (M := M')]
    obtain ⟨h₁, h₂⟩ := LTy.emit_fst_snd (M := M) (M' := M') t n
    rw [h₁, h₂]
    obtain ⟨h₃, h₄⟩ := LTy.emitList_fst_snd (M := M) (M' := M') ts (t.emit (M := M') n).2.2
    exact ⟨by rw [h₃], h₄⟩

theorem LTy.emitFields_fst_snd {M M' : Type} : ∀ (fs : List (String × LTy)) (n : Nat),
    (LTy.emitFields (M := M) fs n).1 = (LTy.emitFields (M := M') fs n).1 ∧
      (LTy.emitFields (M := M) fs n).2.2 = (LTy.emitFields (M := M') fs n).2.2
  | [], _ => ⟨rfl, rfl⟩
  | (l, t) :: fs, n => by
    rw [LTy.emitFields_cons, LTy.emitFields_cons (M := M')]
    obtain ⟨h₁, h₂⟩ := LTy.emit_fst_snd (M := M) (M' := M') t n
    rw [h₁, h₂]
    obtain ⟨h₃, h₄⟩ := LTy.emitFields_fst_snd (M := M) (M' := M') fs (t.emit (M := M') n).2.2
    exact ⟨by rw [h₃], h₄⟩
end

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

/-- A type export under the name `nm` re-pushes the exported type and records a type export. -/
theorem instDef_namedExport (sc : Scope E) (nm : String) {n : Nat}
    {ty : Types.TypeDef RtId E.ExternType} (h : sc.frame.types[n]? = some ty) :
    instantiateDef R inst outer args sc (.export_ { name := nm } ⟨.type, n⟩ none) =
      (pure { frame := { sc.frame with types := sc.frame.types ++ [ty] },
              exports := sc.exports ++ [(nm, .type ty)] } : P E σ (Scope E)) := by
  simp only [instantiateDef, Frame.get?, Frame.type?, h, Option.map_some, need,
    orTrap, Function.comp_apply, Entry.toItem?, pushEntry, Frame.push]
  rfl

theorem PureTys.namedExport (sc : Scope E) (nm : String) {n : Nat}
    {ty : Types.TypeDef RtId E.ExternType} (h : sc.frame.types[n]? = some ty) :
    PureTys R inst outer args sc [.export_ { name := nm } ⟨.type, n⟩ none]
      { frame := { sc.frame with types := sc.frame.types ++ [ty] },
        exports := sc.exports ++ [(nm, .type ty)] }
      (sc.frame.types.length + 1) :=
  ⟨foldlM_single (instDef_namedExport sc nm h), ⟨_, rfl⟩, List.length_append,
    funcExports_append_type _ _ _,
    fun _ hd => by rw [List.mem_singleton.1 hd]; intro _ _ e; cases e⟩

/-- A record type definition followed by its export under the name `nm`. -/
theorem PureTys.recordExport (sc : Scope E) (nm : String) {d : Syntax.DefValType}
    {t : WIT.ClosedType RtId} (h : resolveDefValType? sc.frame d = some t) :
    ∃ sc', PureTys R inst outer args sc
        [.type (.val d), .export_ { name := nm } ⟨.type, sc.frame.types.length⟩ none] sc'
        (sc.frame.types.length + 2) ∧
      Res sc'.frame.types (.idx (sc.frame.types.length + 1)) t := by
  have h₁ := PureTys.val (R := R) (inst := inst) (outer := outer) (args := args) sc h
  have hl : (sc.frame.types ++ [.val t])[sc.frame.types.length]? = some (.val t) := by simp
  have h₂ := PureTys.namedExport (R := R) (inst := inst) (outer := outer) (args := args)
    { sc with frame := { sc.frame with types := sc.frame.types ++ [.val t] } } nm hl
  refine ⟨_, (h₁.trans h₂).cast rfl (by simp), Res.idx ?_⟩
  simp

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem mapM_res {f : Frame E} {tys : List (Types.TypeDef RtId E.ExternType)}
    (hf : tys <+: f.types) :
    ∀ {vs : List Syntax.VT} {ts : List (WIT.ClosedType RtId)}, List.Forall₂ (Res tys) vs ts →
      vs.mapM (resolveValType? f) = some ts
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hr hs => by
    rw [List.mapM_cons, hr f hf, mapM_res hf hs]
    rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem mapM_resFields {f : Frame E} {tys : List (Types.TypeDef RtId E.ExternType)}
    (hf : tys <+: f.types) :
    ∀ {vs : List (String × Syntax.VT)} {ts : List (String × WIT.ClosedType RtId)},
      List.Forall₂ (fun a b => a.1 = b.1 ∧ Res tys a.2 b.2) vs ts →
      vs.mapM (fun (p : String × Syntax.VT) => (p.1, ·) <$> resolveValType? f p.2) = some ts
  | [], [], .nil => rfl
  | (n, _) :: _, (n', _) :: _, .cons ⟨hn, hr⟩ hs => by
    have hn' : n = n' := hn
    subst hn'
    rw [List.mapM_cons, mapM_resFields hf hs, hr f hf]
    rfl

mutual
/-- **The definitions emitted for a type run without a machine operation** and the emitted
value type resolves to `t.toClosed`. -/
theorem LTy.emit_run : ∀ (t : LTy) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc (t.emit (M := E.Module) sc.frame.types.length).2.1 sc'
        (t.emit (M := E.Module) sc.frame.types.length).2.2 ∧
      Res sc'.frame.types (t.emit (M := E.Module) sc.frame.types.length).1 t.toClosed
  | .s32, sc => ⟨sc, PureTys.nil sc, Res.prim _ .s32⟩
  | .u32, sc => ⟨sc, PureTys.nil sc, Res.prim _ .u32⟩
  | .s64, sc => ⟨sc, PureTys.nil sc, Res.prim _ .s64⟩
  | .tuple t ts, sc => by
    obtain ⟨sc₀, hP₀, hR₀⟩ := LTy.emit_run t sc
    obtain ⟨sc₀', hP₀', hR₀'⟩ := LTy.emitList_run ts sc₀
    have hl₀ : sc₀.frame.types.length = (t.emit (M := E.Module) sc.frame.types.length).2.2 :=
      hP₀.2.2.1
    have hc : ∃ sc₁, PureTys R inst outer args sc
        (LTy.emitList (M := E.Module) (t :: ts) sc.frame.types.length).2.1 sc₁
        (LTy.emitList (M := E.Module) (t :: ts) sc.frame.types.length).2.2 ∧
      List.Forall₂ (Res sc₁.frame.types)
        (LTy.emitList (M := E.Module) (t :: ts) sc.frame.types.length).1
        (LTy.toClosedList (t :: ts)) := by
      rw [LTy.emitList_cons, ← hl₀]
      exact ⟨sc₀', hP₀.trans hP₀', .cons (hR₀.mono hP₀'.prefix) hR₀'⟩
    obtain ⟨sc₁, hP₁, hR₁⟩ := hc
    have hl₁ : sc₁.frame.types.length =
        (LTy.emitList (M := E.Module) (t :: ts) sc.frame.types.length).2.2 := hP₁.2.2.1
    have hres : resolveDefValType? sc₁.frame
        (.tuple (LTy.emitList (M := E.Module) (t :: ts) sc.frame.types.length).1) =
          some (.tuple (LTy.toClosedList (t :: ts))) := by
      simp only [resolveDefValType?, mapM_res (List.prefix_refl _) hR₁, Option.map_eq_map,
        Option.map_some]
    have hP₂ := PureTys.val (R := R) (inst := inst) (outer := outer) (args := args) sc₁ hres
    rw [LTy.emit_tuple, ← hl₁]
    refine ⟨_, hP₁.trans hP₂, Res.idx ?_⟩
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]
    rfl
  | .record name l t fs, sc => by
    obtain ⟨sc₀, hP₀, hR₀⟩ := LTy.emit_run t sc
    obtain ⟨sc₀', hP₀', hR₀'⟩ := LTy.emitFields_run fs sc₀
    have hl₀ : sc₀.frame.types.length = (t.emit (M := E.Module) sc.frame.types.length).2.2 :=
      hP₀.2.2.1
    have hc : ∃ sc₁, PureTys R inst outer args sc
        (LTy.emitFields (M := E.Module) ((l, t) :: fs) sc.frame.types.length).2.1 sc₁
        (LTy.emitFields (M := E.Module) ((l, t) :: fs) sc.frame.types.length).2.2 ∧
      List.Forall₂ (fun a b => a.1 = b.1 ∧ Res sc₁.frame.types a.2 b.2)
        (LTy.emitFields (M := E.Module) ((l, t) :: fs) sc.frame.types.length).1
        (LTy.toClosedFields ((l, t) :: fs)) := by
      rw [LTy.emitFields_cons, ← hl₀]
      exact ⟨sc₀', hP₀.trans hP₀', .cons ⟨rfl, hR₀.mono hP₀'.prefix⟩ hR₀'⟩
    obtain ⟨sc₁, hP₁, hR₁⟩ := hc
    have hl₁ : sc₁.frame.types.length =
        (LTy.emitFields (M := E.Module) ((l, t) :: fs) sc.frame.types.length).2.2 := hP₁.2.2.1
    have hres : resolveDefValType? sc₁.frame
        (.record (LTy.emitFields (M := E.Module) ((l, t) :: fs) sc.frame.types.length).1) =
          some (.record (LTy.toClosedFields ((l, t) :: fs))) := by
      have hm := mapM_resFields (f := sc₁.frame) (List.prefix_refl _) hR₁
      simp only [resolveDefValType?]
      rw [hm]
      rfl
    obtain ⟨sc₂, hP₂, hR₂⟩ := PureTys.recordExport (R := R) (inst := inst) (outer := outer)
      (args := args) sc₁ name hres
    rw [LTy.emit_record, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, hR₂⟩
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

/-- `LTy.emit_run` on lists. -/
theorem LTy.emitList_run : ∀ (ts : List LTy) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc
        (LTy.emitList (M := E.Module) ts sc.frame.types.length).2.1 sc'
        (LTy.emitList (M := E.Module) ts sc.frame.types.length).2.2 ∧
      List.Forall₂ (Res sc'.frame.types)
        (LTy.emitList (M := E.Module) ts sc.frame.types.length).1 (LTy.toClosedList ts)
  | [], sc => ⟨sc, PureTys.nil sc, .nil⟩
  | t :: ts, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := LTy.emit_run t sc
    obtain ⟨sc₂, hP₂, hR₂⟩ := LTy.emitList_run ts sc₁
    have hl₁ : sc₁.frame.types.length = (t.emit (M := E.Module) sc.frame.types.length).2.2 :=
      hP₁.2.2.1
    rw [LTy.emitList_cons, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, .cons (hR₁.mono hP₂.prefix) hR₂⟩

/-- `LTy.emit_run` on labelled fields. -/
theorem LTy.emitFields_run : ∀ (fs : List (String × LTy)) (sc : Scope E),
    ∃ sc', PureTys R inst outer args sc
        (LTy.emitFields (M := E.Module) fs sc.frame.types.length).2.1 sc'
        (LTy.emitFields (M := E.Module) fs sc.frame.types.length).2.2 ∧
      List.Forall₂ (fun a b => a.1 = b.1 ∧ Res sc'.frame.types a.2 b.2)
        (LTy.emitFields (M := E.Module) fs sc.frame.types.length).1 (LTy.toClosedFields fs)
  | [], sc => ⟨sc, PureTys.nil sc, .nil⟩
  | (l, t) :: fs, sc => by
    obtain ⟨sc₁, hP₁, hR₁⟩ := LTy.emit_run t sc
    obtain ⟨sc₂, hP₂, hR₂⟩ := LTy.emitFields_run fs sc₁
    have hl₁ : sc₁.frame.types.length = (t.emit (M := E.Module) sc.frame.types.length).2.2 :=
      hP₁.2.2.1
    rw [LTy.emitFields_cons, ← hl₁]
    exact ⟨sc₂, hP₁.trans hP₂, .cons ⟨rfl, hR₁.mono hP₂.prefix⟩ hR₂⟩
end

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
