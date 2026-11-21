module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceReservations

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable

private def Preserves {Value : Type} (table : RT) (operation : Resolve Value) : Prop :=
  ∀ {before after value}, LiveSlots table before.val → operation.run before = .ok (value, after) →
    LiveSlots table after.val

private theorem preservesPure {Value : Type} (table : RT) (value : Value) :
    Preserves table (pure value) := by
  intro before after observed live success
  cases success
  exact live

private theorem preservesBind {Value Result : Type} {table : RT} {operation : Resolve Value}
    {next : Value → Resolve Result} (first : Preserves table operation)
    (second : ∀ value, Preserves table (next value)) : Preserves table (operation >>= next) := by
  intro before after result live success
  rw [StateT.run_bind] at success
  cases intermediate : operation.run before with
  | error issue =>
    rw [intermediate] at success
    change Except.error issue = Except.ok _ at success
    cases success
  | ok pair =>
    rw [intermediate] at success
    change (next pair.1).run pair.2 = Except.ok _ at success
    exact second pair.1 (first live intermediate) success

private theorem preservesMap {Value Result : Type} {table : RT} {operation : Resolve Value}
    (made : Preserves table operation) (map : Value → Result) : Preserves table (map <$> operation) :=
  preservesBind made fun value => preservesPure table (map value)

private theorem preservesReserve (table : RT) (resource : Nat) (slot : BitVec 32) :
    Preserves table (reserve table resource slot) := by
  intro before after value live success
  have looked := WitOwnReferenceTable.reserve_rep table resource slot before after value success
  simp only [reserve, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    set, pure, Except.pure, StateT.get, Except.bind] at success
  split at success
  · cases checked : lookupChecked table resource slot with
    | error issue => rw [checked] at success; cases success
    | ok rep =>
      rw [checked] at success
      cases success
      intro index member
      rcases List.mem_cons.mp member with same | old
      · exact ⟨resource, value, same ▸ looked⟩
      · exact live index old
  · cases success

private theorem preservesList {Input Value : Type} {table : RT} {operation : Input → Resolve Value}
    (step : ∀ value, Preserves table (operation value)) (input : List Input) :
    Preserves table (input.mapM operation) := by
  induction input with
  | nil => exact preservesPure table []
  | cons head tail ih =>
    rw [List.mapM_cons]
    exact preservesBind (step head) fun _ => preservesBind ih fun _ => preservesPure table _

private theorem preservesSized {Input Value : Type} {table : RT} {operation : Input → Resolve Value}
    (step : ∀ value, Preserves table (operation value)) (input : List Input) :
    Preserves table (resolveSized operation input) := by
  induction input with
  | nil => exact preservesPure table _
  | cons head tail ih =>
    rw [resolveSized]
    exact preservesBind (step head) fun _ => preservesBind ih fun _ => preservesPure table _

mutual
private theorem preservesResolve (table : RT) : (type : PTy) → (raw : (rawType type).Val) →
    Preserves table (resolve table type raw)
  | .own resource, index => preservesReserve table resource index.toBitVec
  | .list element, values => preservesList (preservesResolve table element) values
  | .fixedList element _, values =>
    preservesBind (preservesSized (preservesResolve table element) values.toList) fun _ => preservesPure table _
  | .record fields, values => preservesFields table fields values
  | .tuple types, values => preservesTypes table types values
  | .variant cases, value => preservesCases table cases value
  | .option _, none => preservesPure table none
  | .option element, some value => preservesMap (preservesResolve table element value) some
  | .result ok _, .inl value => preservesMap (preservesOpt table ok value) Sum.inl
  | .result _ error, .inr value => preservesMap (preservesOpt table error value) Sum.inr
  | .bool, value | .s32, value | .u32, value | .s64, value | .u64, value | .string, value
  | .s8, value | .u8, value | .s16, value | .u16, value | .f32, value | .f64, value
  | .char, value | .enum _, value | .flags _, value => preservesPure table value
  | .borrow _, value => nomatch value
termination_by structural type => type

private theorem preservesTypes (table : RT) : (types : List PTy) → (raw : PTy.Vals (rawTypes types)) →
    Preserves table (resolveTypes table types raw)
  | [], _ => preservesPure table ()
  | type :: types, (head, tail) =>
    preservesBind (preservesResolve table type head) fun _ =>
      preservesBind (preservesTypes table types tail) fun _ => preservesPure table _
termination_by structural types => types

private theorem preservesFields (table : RT) : (fields : List (String × PTy)) →
    (raw : PTy.FieldVals (rawFields fields)) → Preserves table (resolveFields table fields raw)
  | [], _ => preservesPure table ()
  | (_, type) :: fields, (head, tail) =>
    preservesBind (preservesResolve table type head) fun _ =>
      preservesBind (preservesFields table fields tail) fun _ => preservesPure table _
termination_by structural fields => fields

private theorem preservesCases (table : RT) : (cases : List (String × Option PTy)) →
    (raw : PTy.CaseVals (rawCases cases)) → Preserves table (resolveCases table cases raw)
  | [], raw => nomatch raw
  | (_, type) :: _, .inl value => preservesMap (preservesOpt table type value) Sum.inl
  | _ :: cases, .inr value => preservesMap (preservesCases table cases value) Sum.inr
termination_by structural cases => cases

private theorem preservesOpt (table : RT) : (type : Option PTy) → (raw : PTy.OptVal (rawOpt type)) →
    Preserves table (resolveOpt table type raw)
  | none, _ => preservesPure table ()
  | some type, value => preservesResolve table type value
termination_by structural type => type
end

theorem resolveTypes_live (table : RT) (types : List PTy) (raw : PTy.Vals (rawTypes types))
    {before after : Reservations} {values : PTy.Vals types} (live : LiveSlots table before.val)
    (success : (resolveTypes table types raw).run before = .ok (values, after)) :
    LiveSlots table after.val := preservesTypes table types raw live success

private theorem killAll_cons (table : RT) (slot : BitVec 32) (tail : List (BitVec 32))
    (fresh : slot ∉ tail) :
    (table.killAll [slot]).killAll tail = table.killAll (slot :: tail) := by
  funext index
  by_cases same : index = slot
  · subst index
    simp [RT.killAll, fresh]
  · simp [RT.killAll, same]

theorem commit_of_live {E : CoreEngine} (limits : Component.Limits) (cx : LiftLowerContext E)
    (slots : List (BitVec 32)) (table : RT) (store : CStore E)
    (distinct : slots.Nodup) (live : LiveSlots table slots) (matched : Matches table store cx.inst) :
    ∃ owners final, Commit limits cx store slots owners final ∧ Matches (table.killAll slots) final cx.inst := by
  induction slots generalizing table store with
  | nil => exact ⟨[], store, .nil store, matched⟩
  | cons slot tail ih =>
    obtain ⟨resource, rep, found⟩ := live slot (by simp)
    obtain ⟨owner, observed, _, taken, next⟩ :=
      WitOwnReferenceTable.lookup_refines_take limits cx store table (⟨resource⟩ : RtId) slot rep matched found
    have notInTail := (List.nodup_cons.mp distinct).1
    have tailLive : LiveSlots (table.killAll [slot]) tail := by
      intro index member
      obtain ⟨ty, value, lookup⟩ := live index (List.mem_cons_of_mem slot member)
      have different : index ≠ slot := fun equals => notInTail (equals ▸ member)
      exact ⟨ty, value, by simpa [RT.lookup, RT.killAll, different] using lookup⟩
    obtain ⟨owners, final, moves, finalMatch⟩ := ih _ _ (List.nodup_cons.mp distinct).2 tailLive next
    exact ⟨_, final, .cons observed taken moves, by simpa only [killAll_cons table slot tail notInTail] using finalMatch⟩

theorem reserveOp_commit {E : CoreEngine} (limits : Component.Limits) (cx : LiftLowerContext E)
    (store : CStore E) (table : RT) (sig : WitSig) (raw : Op (rawSignature sig))
    (matched : Matches table store cx.inst) {node : Op sig} {reserved : Reservations}
    (success : reserveOp sig table raw = .ok (node, reserved)) :
    ∃ owners final, Commit limits cx store reserved.val.reverse owners final ∧
      Matches (table.killAll reserved.val) final cx.inst := by
  have live : LiveSlots table reserved.val := by
    unfold reserveOp at success
    cases schema : checkPTys .recursiveOwn (sig.params raw.1) with
    | error issue => simp [schema, Except.mapError, bind, Except.bind] at success
    | ok accepted =>
      cases decoded : (resolveTypes table (sig.params raw.1) raw.2).run ⟨[], .nil⟩ with
      | error issue => simp [schema, decoded, Except.mapError, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨values, reservations⟩ := pair
        have preserves := resolveTypes_live table (sig.params raw.1) raw.2 (by simp [LiveSlots]) decoded
        simp [schema, decoded, Except.mapError, bind, Except.bind] at success
        cases success
        exact preserves
  have reverseLive : LiveSlots table reserved.val.reverse := fun slot member => live slot (by simpa using member)
  obtain ⟨owners, final, commits, observed⟩ :=
    commit_of_live limits cx reserved.val.reverse table store (List.nodup_reverse.mpr reserved.property)
      reverseLive matched
  exact ⟨owners, final, commits, by simpa [Matches, RT.lookup, RT.killAll] using observed⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceReservations
