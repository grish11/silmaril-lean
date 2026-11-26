module

public import Silmaril.Wasm.Component.SyncImportITree.Defs
public import Silmaril.Wasm.Game.Machine.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.SyncImportITree

open Silmaril.Games Silmaril.Wasm.Game
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Execution.Core (Step)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile ofFlat toFlat?)

variable {c : SimpleI} {o : GrowOracle} {r : Ready c} {q : Question (exportIface c)}
  {f : r.inst.F.Op} {x : Cursor}

private theorem lower_types {ts : List ValTy} {vs : List Silmaril.Wasm.Component.Val} (h : ValTy.checkList ts vs = true) :
    List.Forall₂ ScalarType.HasVal ((ValTy.flatList ts).map .num) ((lowerArgs ts vs).map ofFlat) := by
  have flatTypes : (lowerArgs ts vs).map (·.type) = ValTy.flatList ts := by
    induction ts generalizing vs with
    | nil => rfl
    | cons t ts ih =>
      cases vs with
      | nil => cases h
      | cons v vs =>
        obtain ⟨hv, hs⟩ := Bool.and_eq_true_iff.mp h
        show (t.lower v ++ lowerArgs ts vs).map (·.type) = t.flat ++ ValTy.flatList ts
        rw [List.map_append, ValTy.lower_types t v hv, ih hs]
  rw [← flatTypes, List.map_map]
  generalize lowerArgs ts vs = xs
  induction xs with
  | nil => exact .nil
  | cons v _ ih => exact .cons ⟨v.bits, rfl⟩ ih

theorem entry_exists (r : Ready c) (q : Question (exportIface c)) :
    ∃ f, entry r q = some f := by
  let i : Fin c.exports.length := Fin.cast (by simp [exportIface]) q.index
  let e := c.exports[i]
  have et : (exportIface c)[q.index].2 = e.ty := by
    exact congrArg Prod.snd
      (List.getElem_map (fun v : SimpleExport => (v.name, v.ty)) (l := c.exports)
        (i := q.index.val) (h := by simpa [exportIface] using q.index.isLt))
  obtain ⟨nm, he⟩ := r.good.core e (List.getElem_mem i.isLt)
  have hf : r.inst.exports[e.core]? = some (fnOf e.ty.flat) := by
    rw [r.isInst.2.2, List.getElem?_map, he]
    rfl
  have hi : e.core < r.inst.exports.length := List.getElem?_eq_some_iff.mp hf |>.choose
  have hft : r.inst.exports.get ⟨e.core, hi⟩ = fnOf e.ty.flat :=
    Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hf)
  have ht := lower_types q.args.property
  change (∃ f, ifaceOp? r.inst.exports e.core
    ((lowerArgs (exportIface c)[q.index].2.params q.args.val).map ofFlat) = some f)
  unfold ifaceOp?
  rw [dite_eq_left hi]
  split
  · exact ⟨_, rfl⟩
  · rename_i hn
    rw [hft, ← et] at hn
    exact False.elim (hn ht)

private theorem lowered_result {ft : FuncTy} {t : FnType} (ht : t = fnOf ft.flat)
    (a : Option (Values ft.results)) :
    (payloadAnswer t ((a.map fun vs => Payload.vals vs.val).bind (Adapter.lower ft).up)).toResult =
      match a with
      | none => .trap
      | some vs => .values ((lowerArgs ft.results vs.val).map ofFlat) := by
  subst t
  cases a with
  | none => rfl
  | some vs =>
    change (payloadAnswer (fnOf ft.flat) ((checkLower ft.results vs.val).map Payload.flat)).toResult = _
    rw [checkLower, ite_eq_left vs.property]
    have h : List.Forall₂ ScalarType.HasVal (fnOf ft.flat).results
        ((lowerArgs ft.results vs.val).map ofFlat) := lower_types vs.property
    simp only [Option.map_some, payloadAnswer, typed?, dite_eq_left h]
    rfl

theorem request_resumes {m : Question c.imports} {k : m.Answer → Cursor}
    (reached : ReachesFront o r q f x (.request m k)) (a : m.Answer) :
    ∃ (e : r.inst.E.Op) (p : Cursor) (b : r.inst.E.Ar e),
      ReachesCut o r.inst f x (.request e p) ∧
      r.inst.Trans (profile o) (.waiting f p.1 p.2 e) (.inl (.ans e b))
        (.running f (k a).1 (k a).2) ∧
      b.toResult = (match a with
        | none => .trap
        | some vs => .values ((lowerArgs c.imports[m.index].2.results vs.val).map
            Silmaril.Wasm.SingleThreaded.ofFlat)) ∧
      ImpRel c r.inst ⟨e, b⟩ [⟨(m.index, .vals m.args.val), a.map (fun vs => .vals (Subtype.val vs))⟩] ∧
      ∃ h args, CalloutAt p.1 p.2 h args ∧
        Step (profile o) (answerHost h args b.toResult) (p.2.config p.1) ((k a).2.config (k a).1) := by
  rcases reached with ⟨cut, hc, hf⟩ | ⟨_, eq⟩
  · cases cut with
    | reply b s => cases hf
    | request e p =>
      simp only [cutFront] at hf
      split at hf
      next hi =>
        let i : Fin c.imports.length := ⟨e.1.val, hi⟩
        cases hr : liftArgs c.imports[i].2.params (e.2.val.filterMap toFlat?) with
        | none =>
          have hl : liftValues c.imports[i].2.params (e.2.val.filterMap toFlat?) = none :=
            Option.pmap_none' hr
          rw [hl] at hf
          cases hf
        | some ws =>
          have hl : liftValues c.imports[i].2.params (e.2.val.filterMap toFlat?) =
              some ⟨ws, checkList_of_liftArgs hr⟩ := Option.pmap_some' hr
          rw [hl] at hf
          simp only [Front.request.injEq] at hf
          obtain ⟨rfl, hk⟩ := hf
          have hk' := eq_of_heq hk
          subst k
          let R : Option Payload := a.map (fun vs => .vals (Subtype.val vs))
          let A := R.bind (Adapter.lower c.imports[i].2).up
          let b := payloadAnswer (r.inst.imports.get e.1) A
          refine ⟨e, p, b, hc, .uret b, ?_, ?_, ?_⟩
          · have hft : r.inst.imports[e.1.val]? = some (fnOf c.imports[i].2.flat) := by
              calc
                _ = (c.mod.imports.map fun p => fnOf p.2)[e.1.val]? :=
                  congrArg (fun l : List FnType => l[e.1.val]?) r.isInst.2.1
                _ = _ := by
                  rw [r.good.imports, List.getElem?_map, List.getElem?_map,
                    List.getElem?_eq_getElem hi]
                  rfl
            have ht : r.inst.imports.get e.1 = fnOf c.imports[i].2.flat :=
              Option.some.inj ((List.getElem?_eq_getElem e.1.isLt).symm.trans hft)
            cases a with
            | none => rfl
            | some vs => exact lowered_result ht (some vs)
          · refine ⟨c.imports[i].1, c.imports[i].2, A, ?_, rfl, ?_⟩
            · rw [List.getElem?_eq_getElem hi]
              rfl
            · rw [hr]
              exact ⟨hi, R, rfl, rfl⟩
          · unfold ReachesCut at hc
            cases hc with
            | ucall _ hcall _ => exact ⟨_, _, hcall, calloutAt_step hcall ⟨rfl, rfl, rfl⟩⟩
      next => cases hf
  · cases eq

end Silmaril.Proofs.Wasm.Component.SyncImportITree
