module

public import Silmaril.Proofs.Wasm.Interp.XClassify
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryAux
public import Silmaril.Wasm.Abstract.CallRes.Thms
public import Silmaril.Wasm.Binaryen.Pass.DirectizeCast

/-!
# Resolution at a typed indirect call (proofs)

At a `call_indirect x y` (or `return_call_indirect x y`) site typed in context, in an instance
with valid types, the index on top of the stack resolves (`callIndirect_res`): Core's
`table.get; ref.cast; call_ref` chain has an outcome (`CallRes.IndRes`). The table exists (the
site's frame is typed: `ContextTyped.fragment_ctx`, `StateOk.table?`), and a table entry passing
the cast to `ref null y` is null or a function reference (`refTo_classify`), so the stuck case
of `CallRes.indRes_cases` cannot occur.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

theorem emptyOk_empty : (({} : TypeCtx)).EmptyOk := fun _ h => by simp at h

/-- **A typed `call_indirect x y` site resolves.** -/
theorem indirect_res {s : Store H} {f : Frame} {stk : List Val} {x : TableIdx} {y : TypeIdx}
    {rest : List Admin} {i : Instr} (hi : i = .callIndirect x y ∨ i = .returnCallIndirect x y)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩) :
    ∃ (ad : AddrType) (j : BitVec ad.intType.width) (stk' : List Val) (o : Option Nat),
      stk = .num ⟨.int ad.intType, j⟩ :: stk' ∧ Abstract.CallRes.IndRes s f x y ad j o := by
  rcases hi with rfl | rfl <;>
  · have typed : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.plain _]⟩ :=
      Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
        List.singleton_append] using ht)
    obtain ⟨C, ts, xs, hs, hC, hctx, hcode⟩ := typed.fragment_ctx
    obtain ⟨mid, xs₁, _, hp, hi', _⟩ :=
      AdminsOk.split hcode hC (vals stk.reverse) [.plain _] rfl (by simp)
    obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
    have hC' := hC.initLocals xs₁
    obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hi'
    have hinstr := ha.plain_inv_ne
    obtain ⟨a, l, rt, d, ps, rs, pre, htab, hd, he, hpar⟩ : ∃ (a : AddrType) (l : Limits)
        (rt : CRefType) (d : DefType) (ps rs : Ty (.list .val)) (pre : List CValType),
        (C.initLocals xs₁).tables[x.toNat]? = some ⟨a, l, rt⟩ ∧ (C.initLocals xs₁).type? y = some d ∧
        Expand d (.func ps rs) ∧ it.params = pre ++ [a.valType] := by
      generalize C.initLocals xs₁ = C₀ at hinstr ⊢
      first
      | (cases hinstr with
        | callIndirect ht hs hd he => exact ⟨_, _, _, _, _, _, _, ht, hd, he, rfl⟩
        | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
          cases h)
      | (cases hinstr with
        | @returnCallIndirect _ _ _ _ _ _ _ ps _ _ t₃ _ ht hs hd he =>
          exact ⟨_, _, _, _, _, _, t₃ ++ ps.toList, ht, hd, he, by simp⟩
        | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
          cases h)
    have hΔ : (C.initLocals xs₁).toTypeCtx = C.toTypeCtx := Context.initLocals_toTypeCtx C xs₁
    -- the index on top of the stack
    have h : List.Forall₂ (Sub (C.initLocals xs₁).toTypeCtx) mid (framed ++ (pre ++ [a.valType])) := by
      have := hsub'.1; rw [hpar] at this; exact this
    simp only [← List.append_assoc] at h
    obtain ⟨l', tr, rfl, -, hr⟩ := forall₂_lastR h
    simp only [List.nil_append, ResultSub] at hsub
    obtain ⟨p', pr, rfl, -, hs₁⟩ := forall₂_lastR hsub
    obtain ⟨vs', v, hve, -, hvr⟩ := forall₂_lastR hv
    have hstk : stk = v :: vs'.reverse := by
      have := congrArg List.reverse hve
      simpa using this
    rw [hΔ] at hr
    have hto : ValTo s C.toTypeCtx v a.valType := ⟨pr, hvr, (Relation.ReflTransGen.single hs₁).tail hr⟩
    have hvok := hto.valOk_of_numVec (by cases a <;> simp [numVec, AddrType.valType])
    obtain ⟨j, rfl⟩ := ValOk.int_inv (t := a.intType) hvok
    -- the table and the annotated type, through the site's typed frame
    obtain ⟨Cf, hfr, hfv, -⟩ := hctx.frame
    have hst : StateOk s f Cf := ⟨hs, hfr⟩
    have htabs : (C.initLocals xs₁).tables = Cf.tables := by
      have h1 := congrArg Context.tables (Context.initLocals_frameView C xs₁)
      have h2 := congrArg Context.tables hfv
      simp only [Context.frameView] at h1 h2
      rw [h1, h2]
    have htysC : C.types = f.module.types := by
      have h2 := congrArg (fun C : Context => C.types) hfv
      simp only [Context.frameView] at h2
      rw [h2]; exact hfr.types_eq
    obtain ⟨ta, ti, hta⟩ := StateOk.table? hst (by rw [← htabs]; exact htab)
    have hdm : f.module.types[y.toNat]? = some d := by
      simpa [Context.type?, htysC] using hd
    refine ⟨a, j, vs'.reverse, ?_⟩
    rcases Abstract.CallRes.indRes_cases (y := y) (i := j) hta with ⟨o, ho⟩ | ⟨r, -, hnn, hnf, hok⟩
    · exact ⟨o, hstk, ho⟩
    · rw [Abstract.CallRes.castTo, Binaryen.DirectizeCast.instRef_typeIdx hdm] at hok
      have hto' : ValTo s ({} : TypeCtx) (.ref r) (Ty.refT true (Ty.defHeap d)) :=
        ⟨_, .ref hok, .refl⟩
      rcases refTo_classify hs emptyOk_empty he hto' with rfl | ⟨fa, -, rfl, -⟩
      · exact absurd rfl hnn
      · exact absurd rfl (hnf fa)

end Silmaril.Wasm.Interp
