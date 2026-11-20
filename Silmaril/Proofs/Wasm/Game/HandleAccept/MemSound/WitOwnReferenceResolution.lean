module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceResolution

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable

variable {E : CoreEngine} {inst : InstId} {table : RT}

private def Refines {Value : Type} (inst : InstId) (table : RT) (atomic : Resolve Value)
    (eager : Eager E Value) : Prop :=
  ∀ {before after state value}, state.Matches inst table before →
    atomic.run before = .ok (value, after) →
    ∃ final, eager.run.run state = (.ok value, final) ∧ final.Matches inst table after

private theorem refinesPure {Value : Type} (value : Value) :
    Refines (E := E) inst table (pure value) (pure value) := by
  intro before after state observed matched success
  cases success
  exact ⟨state, rfl, matched⟩

private theorem refinesBind {Value Result : Type} {atomic : Resolve Value} {eager : Eager E Value}
    {nextAtomic : Value → Resolve Result} {nextEager : Value → Eager E Result}
    (first : Refines inst table atomic eager)
    (rest : ∀ value, Refines inst table (nextAtomic value) (nextEager value)) :
    Refines inst table (atomic >>= nextAtomic) (eager >>= nextEager) := by
  intro before after state value matched success
  rw [StateT.run_bind] at success
  cases intermediate : atomic.run before with
  | error issue =>
    rw [intermediate] at success
    change Except.error issue = Except.ok _ at success
    cases success
  | ok pair =>
    rw [intermediate] at success
    change (nextAtomic pair.1).run pair.2 = Except.ok _ at success
    obtain ⟨updated, taken, stillMatched⟩ := first matched intermediate
    obtain ⟨final, finished, finallyMatched⟩ := rest pair.1 stillMatched success
    refine ⟨final, ?_, finallyMatched⟩
    change (ExceptT.bindCont nextEager (eager.run.run state).1).run (eager.run.run state).2 = _
    rw [taken]
    exact finished

private theorem refinesMap {Value Result : Type} {atomic : Resolve Value} {eager : Eager E Value}
    (first : Refines inst table atomic eager) (map : Value → Result) :
    Refines inst table (map <$> atomic) (map <$> eager) :=
  refinesBind first fun value => refinesPure (map value)

private theorem refinesReserve (limits : Component.Limits) (cx : LiftLowerContext E)
    (table : RT) (resource : Nat) (slot : BitVec 32) :
    Refines cx.inst table (reserve table resource slot) (takeIndex limits cx resource slot) := by
  intro before after state value matched success
  have found := WitOwnReferenceTable.reserve_rep table resource slot before after value success
  simp only [reserve, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    set, pure, Except.pure, StateT.get, Except.bind] at success
  split at success
  · rename_i fresh
    cases checked : lookupChecked table resource slot with
    | error issue => rw [checked] at success; cases success
    | ok rep =>
      rw [checked] at success
      cases success
      have visible : (table.killAll before.val).lookup resource slot = some value := by
        simpa [RT.lookup, RT.killAll, fresh] using found
      obtain ⟨owner, _, represented, moved, updated⟩ :=
        WitOwnReferenceTable.lookup_refines_take limits cx state.store _ ⟨resource⟩ slot value
          matched.1 visible
      refine ⟨⟨ArenaField.insts.modify state.store cx.inst (InstState.removeHandle slot.toNat),
        (slot, ⟨⟨resource⟩, owner⟩) :: state.receipts⟩, ?_, ?_, ?_⟩
      · simp only [takeIndex, ExceptT.run, ExceptT.mk, StateT.run]
        rw [moved]
        simp only [represented]
      · intro ty index
        by_cases same : index = slot
        · subst index
          simpa [RT.lookup, RT.killAll, fresh] using updated ty slot
        · simpa [RT.lookup, RT.killAll, same] using updated ty index
      · exact congrArg (slot :: ·) matched.2
  · cases success

private theorem refinesList {Input Value : Type} {atomic : Input → Resolve Value}
    {eager : Input → Eager E Value} (step : ∀ input, Refines inst table (atomic input) (eager input))
    (input : List Input) : Refines inst table (input.mapM atomic) (input.mapM eager) := by
  induction input with
  | nil => exact refinesPure []
  | cons head tail ih =>
    rw [List.mapM_cons, List.mapM_cons]
    exact refinesBind (step head) fun _ => refinesBind ih fun _ => refinesPure _

private theorem refinesSized {Input Value : Type} {atomic : Input → Resolve Value}
    {eager : Input → Eager E Value} (step : ∀ input, Refines inst table (atomic input) (eager input))
    (input : List Input) : Refines inst table (resolveSized atomic input) (resolveSized eager input) := by
  induction input with
  | nil => exact refinesPure _
  | cons head tail ih =>
    rw [resolveSized, resolveSized]
    exact refinesBind (step head) fun _ => refinesBind ih fun _ => refinesPure _

mutual
private theorem refinesResolve (limits : Component.Limits) (cx : LiftLowerContext E) (table : RT) :
    (type : PTy) → (raw : (rawType type).Val) →
    Refines cx.inst table (resolve table type raw) (resolveWith (takeIndex limits cx) type raw)
  | .own resource, index => refinesReserve limits cx table resource index.toBitVec
  | .list element, values => refinesList (refinesResolve limits cx table element) values
  | .fixedList element _, values =>
    refinesBind (refinesSized (refinesResolve limits cx table element) values.toList) fun _ => refinesPure _
  | .record fields, values => refinesFields limits cx table fields values
  | .tuple types, values => refinesTypes limits cx table types values
  | .variant cases, value => refinesCases limits cx table cases value
  | .option _, none => refinesPure none
  | .option element, some value => refinesMap (refinesResolve limits cx table element value) some
  | .result ok _, .inl value => refinesMap (refinesOpt limits cx table ok value) Sum.inl
  | .result _ error, .inr value => refinesMap (refinesOpt limits cx table error value) Sum.inr
  | .bool, value | .s32, value | .u32, value | .s64, value | .u64, value | .string, value
  | .s8, value | .u8, value | .s16, value | .u16, value | .f32, value | .f64, value
  | .char, value | .enum _, value | .flags _, value => refinesPure value
  | .borrow _, value => nomatch value
termination_by structural type => type

private theorem refinesTypes (limits : Component.Limits) (cx : LiftLowerContext E) (table : RT) :
    (types : List PTy) → (raw : PTy.Vals (rawTypes types)) →
    Refines cx.inst table (resolveTypes table types raw) (resolveTypesWith (takeIndex limits cx) types raw)
  | [], _ => refinesPure ()
  | type :: types, (head, tail) =>
    refinesBind (refinesResolve limits cx table type head) fun _ =>
      refinesBind (refinesTypes limits cx table types tail) fun _ => refinesPure _
termination_by structural types => types

private theorem refinesFields (limits : Component.Limits) (cx : LiftLowerContext E) (table : RT) :
    (fields : List (String × PTy)) → (raw : PTy.FieldVals (rawFields fields)) →
    Refines cx.inst table (resolveFields table fields raw) (resolveFieldsWith (takeIndex limits cx) fields raw)
  | [], _ => refinesPure ()
  | (_, type) :: fields, (head, tail) =>
    refinesBind (refinesResolve limits cx table type head) fun _ =>
      refinesBind (refinesFields limits cx table fields tail) fun _ => refinesPure _
termination_by structural fields => fields

private theorem refinesCases (limits : Component.Limits) (cx : LiftLowerContext E) (table : RT) :
    (cases : List (String × Option PTy)) → (raw : PTy.CaseVals (rawCases cases)) →
    Refines cx.inst table (resolveCases table cases raw) (resolveCasesWith (takeIndex limits cx) cases raw)
  | [], raw => nomatch raw
  | (_, type) :: _, .inl value => refinesMap (refinesOpt limits cx table type value) Sum.inl
  | _ :: cases, .inr value => refinesMap (refinesCases limits cx table cases value) Sum.inr
termination_by structural cases => cases

private theorem refinesOpt (limits : Component.Limits) (cx : LiftLowerContext E) (table : RT) :
    (type : Option PTy) → (raw : PTy.OptVal (rawOpt type)) →
    Refines cx.inst table (resolveOpt table type raw) (resolveOptWith (takeIndex limits cx) type raw)
  | none, _ => refinesPure ()
  | some type, value => refinesResolve limits cx table type value
termination_by structural type => type
end

theorem resolveTypes_refines_eager (limits : Component.Limits) (cx : LiftLowerContext E) (table : RT)
    (types : List PTy) (raw : PTy.Vals (rawTypes types))
    {before after : Reservations} {state : Resolution E} {values : PTy.Vals types}
    (matched : state.Matches cx.inst table before)
    (success : (resolveTypes table types raw).run before = .ok (values, after)) :
    ∃ final, (resolveTypesWith (takeIndex limits cx) types raw).run.run state = (.ok values, final) ∧
      final.Matches cx.inst table after :=
  refinesTypes limits cx table types raw matched success

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceResolution
