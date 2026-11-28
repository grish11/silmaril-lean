module

public import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
public import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Binders.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Defs

/-! The tagged graph and collection adapter for checked source expressions. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Tagged

open Data.Tagged

universe u

@[expose] public section

/-- Inputs to the fixed policy for malformed collection operands. -/
inductive InvalidCollection where
  | function (bound : Value.{u})
  | binderBounds (kind : BinderMap) (bounds : List Value.{u})
  | functionSet (domain range : Value.{u})
  | record (fields : List (String × Value.{u}))
  | recordSet (error : RecordSetError) (fields : List (String × Value.{u}))

abbrev CollectionPolicy := InvalidCollection.{u} → Value.{u}

/-- Fix `invalid` with `policy` across valuations. The domain, range and field
bounds must decode as sets. A malformed collection invokes `invalid` with its
original operands in source order. Graph operations use `unspecified`, with
the same operand and path policies as the mathematical tagged operations. -/
noncomputable def Policy.collectionOperations (policy : Policy.{u})
    (invalid : CollectionPolicy.{u}) (unspecified : Unspecified.{u} := policy.numeric) :
    CollectionOperations Value.{u} where
  toDataOperations := policy.operations
  function := fun bound body =>
    match bound.asSet with
    | some domain => Value.function (Graph.ofFn domain body)
    | none => invalid (.function bound)
  functionSet := fun domain range =>
    match domain.asSet, range.asSet with
    | some s, some t => Value.set (s.functionSet t)
    | _, _ => invalid (.functionSet domain range)
  record := fun fields =>
    let names := fields.map Prod.fst
    if names.Nodup then
      Value.record names (fun name => (fields.lookup name).getD (invalid (.record fields)))
    else invalid (.record fields)
  recordSet := Value.recordSet (fun error fields => invalid (.recordSet error fields))
  domain := Value.domain unspecified
  apply := Value.apply unspecified
  tuple := Value.tuple
  untuple := Value.untuple
  product := Value.cartesian
  invalidBounds := fun kind bounds => invalid (.binderBounds kind bounds)
  string := Value.string
  except := fun root clauses =>
    Value.updateClauses unspecified root (clauses.map fun (keys, replacement) => ⟨keys, replacement⟩)

end
end Silmaril.Logic.Temporal.TLA.DataElab.Tagged
