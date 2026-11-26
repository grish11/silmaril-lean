module

public import Silmaril.Formats.Parquet.ListPage.Defs
import Silmaril.Proofs.Formats.Parquet.ListPage.Correctness

public section

namespace Silmaril.Formats.Parquet.ListPage

theorem readEvent_wire {entry : Nat × Nat × Option Int32} {event : Event}
    (h : readEvent entry = .ok event) : event.wire = entry :=
  Proofs.Formats.Parquet.ListPage.readEvent_wire h

/-- The rows re-emit exactly the original sequence of starts, nulls, and elements. -/
theorem reconstruct_wire {events : List Event} {rows : List Row}
    (h : reconstruct events = .ok rows) : rows.flatMap rowEvents = events :=
  Proofs.Formats.Parquet.ListPage.reconstruct_wire h

theorem reconstruct_continuation (item : Option Int32) (rest : List Event) :
    reconstruct (.next item :: rest) = .error .continuationWithoutList :=
  Proofs.Formats.Parquet.ListPage.reconstruct_continuation item rest

theorem decodeBody_wire {limits : Limits} {expectedRows slots : Nat} {body : Bytes}
    {rows : List Row} (h : decodeBody limits expectedRows slots body = .ok rows) :
    Wire limits expectedRows slots body rows :=
  Proofs.Formats.Parquet.ListPage.decodeBody_wire h

/-- The complete checked page has the declared level slot count, original row
count and exact byte consumption, including both level lengths and PLAIN values. -/
theorem decodeV1_wire {limits : Limits} {codec : Int} {header : Page.Header}
    {expectedRows : Nat} {body : Bytes} {rows : List Row}
    (h : decodeV1 limits codec header expectedRows body = .ok rows) :
    PageWire limits codec header expectedRows body rows :=
  Proofs.Formats.Parquet.ListPage.decodeV1_wire h

end Silmaril.Formats.Parquet.ListPage
