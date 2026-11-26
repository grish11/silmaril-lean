module

public import Silmaril.Wasm.Component.SyncITree.Defs
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Game.Machine.Result.Thms
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Wasm.Component.ABI.Thms
public import Silmaril.Wasm.Game.Termination.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.SyncITree

open Silmaril.Wasm.Component (liftArgs lowerArgs)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.SyncITree
open Silmaril.Wasm.Abstract.BodyTrace
open Silmaril.Wasm.Execution.Core (Result Store)
open Silmaril.Wasm.Game (Reach ResultAt reach_normal_unique resultAt_no_internal
  reach_normal_not_infinite)
open Silmaril.Wasm.SingleThreaded (GrowOracle Thread profile)
open Silmaril.Elgot

variable {c : Simple} {o : GrowOracle} {r : Ready c} {q : Question c}
  {s s' : Store Nat} {a : q.Answer}

private theorem traps_iff (x : SimpleExport) (fs : Option (List Silmaril.Wasm.Component.Flat)) :
    liftOutcome x.ty fs = .traps ↔ fs.bind (liftArgs x.ty.results) = none := by
  cases fs with
  | none => simp [liftOutcome]
  | some fs =>
    cases h : liftArgs x.ty.results fs <;> simp [liftOutcome, h]

private theorem finishes_iff :
    Finishes o r q s a s' ↔
      ∃ t res,
        Reach (profile o)
          (s, Thread.invokeFlat (r.inst.addrs.getD c.exports[q.exportIdx].core 0)
            (lowerArgs c.exports[q.exportIdx].ty.params q.args.val)) (s', t) ∧
        ResultAt s' t res ∧
        (coreRes res).bind (liftArgs c.exports[q.exportIdx].ty.results) = a.map Subtype.val := by
  cases a with
  | none =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨t, res, run, result, trap⟩ := h.run
      exact ⟨t, res, run, result, (traps_iff _ _).mp trap⟩
    · rintro ⟨t, res, run, result, trap⟩
      exact ⟨q.args.property, t, res, run, result, (traps_iff _ _).mpr trap⟩
  | some ws =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨t, vs, fs, run, result, flat, lifted⟩ := h.run
      exact ⟨t, .values vs, run, result, by simpa [coreRes, flat] using lifted⟩
    · rintro ⟨t, res, run, result, lifted⟩
      cases res with
      | values vs =>
        cases flat : coreRes (.values vs) with
        | none => simp [flat] at lifted
        | some fs =>
          exact ⟨q.args.property, t, vs, fs, run, result, flat, by simpa [flat] using lifted⟩
      | trap => simp [coreRes] at lifted
      | throw => simp [coreRes] at lifted

private theorem finishes_unique {a' : q.Answer} {s'' : Store Nat}
    (first : Finishes o r q s a s') (second : Finishes o r q s a' s'') :
    a = a' ∧ s' = s'' := by
  obtain ⟨t, res, run, result, lifted⟩ := finishes_iff.mp first
  obtain ⟨t', res', run', result', lifted'⟩ := finishes_iff.mp second
  have eq := reach_normal_unique run run' (resultAt_no_internal result)
    (resultAt_no_internal result')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
  obtain rfl := result.unique result'
  exact ⟨Option.map_injective Subtype.val_injective (lifted.symm.trans lifted'), rfl⟩

private theorem not_diverges_of_finishes (h : Finishes o r q s a s') :
    ¬ DivAt (profile o) r.inst c.exports[q.exportIdx] q.args.val s := by
  obtain ⟨_, _, run, result, -⟩ := finishes_iff.mp h
  exact fun hd => reach_normal_not_infinite run (resultAt_no_internal result) hd.run

theorem responds_iff : Responds o r q s a s' ↔ Finishes o r q s a s' := by
  classical
  unfold Responds
  by_cases done : ∃ p : q.Answer × Store Nat, Finishes o r q s p.1 p.2
  · have eq : ((body o r q).run ⟨s⟩).run =
        ITree.ret (.ok (⟨.reply done.choose.1⟩, ⟨done.choose.2⟩)) := dite_eq_left done
    rw [toAFun_of_run_ret eq]
    constructor
    · intro h
      have obs := (Set.mem_singleton_iff.mp h).symm
      simp [endOf] at obs
      obtain ⟨rfl, rfl⟩ := obs
      exact done.choose_spec
    · intro h
      obtain ⟨ha, hs⟩ := finishes_unique h done.choose_spec
      simp [ha, hs, endOf]
  · have noFinish : ¬ Finishes o r q s a s' := fun h => done ⟨(a, s'), h⟩
    rw [iff_false_intro noFinish, iff_false]
    by_cases hd : DivAt (profile o) r.inst c.exports[q.exportIdx] q.args.val s
    · have eq : ((body o r q).run ⟨s⟩).run = ITree.diverge :=
        (dite_eq_right done).trans (ite_eq_left hd)
      rintro ⟨cs, _, path, obs⟩
      have empty : cs = [] := by
        cases cs with
        | nil => rfl
        | cons call _ => exact call.1.1.elim0
      subst cs
      cases path with
      | ret h => exact ITree.ret_ne_diverge _ (h.symm.trans eq)
      | div _ => simp [endOf] at obs
    · have eq : ((body o r q).run ⟨s⟩).run = ITree.ret (.ok (⟨.noOutcome⟩, ⟨s⟩)) :=
        (dite_eq_right done).trans (ite_eq_right hd)
      rw [toAFun_of_run_ret eq]
      simp [endOf]

theorem diverges_iff :
    ((body o r q).run ⟨s⟩).run = ITree.diverge ↔
      DivAt (profile o) r.inst c.exports[q.exportIdx] q.args.val s := by
  classical
  simp only [body, StateT.run, ExceptT.run, ExceptT.mk]
  split
  · rename_i done
    rw [iff_false_intro (not_diverges_of_finishes done.choose_spec)]
    exact iff_false_intro (ITree.ret_ne_diverge _)
  · split
    · simp_all
    · simp_all [ITree.ret_ne_diverge]

end Silmaril.Proofs.Wasm.Component.SyncITree
