module

public import Silmaril.Formats.Parquet.NestedPresence.Defs
import Silmaril.Proofs.Formats.Parquet.NestedPresence.Correctness

public section

namespace Silmaril.Formats.Parquet.NestedPresence

theorem classify_contract {child : Child} {level : Nat} (h : level ≤ child.maxDefinition) :
    (classify child level = .parentAbsent ↔ level = 0) ∧
    (classify child level = .childNull ↔ child = .optional ∧ level = 1) ∧
    (classify child level = .value ↔ level = child.maxDefinition) :=
  Proofs.Formats.Parquet.NestedPresence.classify_contract h

theorem decode_wire {child : Child} {slots : Nat} {limits : Limits} {body : Bytes}
    {result : Result} (h : decode child slots limits body = .ok result) :
    Wire child slots limits body result :=
  Proofs.Formats.Parquet.NestedPresence.decode_wire h

theorem decodeV1_wire {child : Child} {limits : Limits} {header : Page.Header} {body : Bytes}
    {result : Result} (h : decodeV1 child limits header body = .ok result) : PageWire child limits header body result :=
  Proofs.Formats.Parquet.NestedPresence.decodeV1_wire h

end Silmaril.Formats.Parquet.NestedPresence
