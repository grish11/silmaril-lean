module

public import Silmaril.Formats.Parquet.Page.Header.Defs
import all Silmaril.Formats.Parquet.Page.Header.Defs
import Silmaril.Formats.ThriftCompact.Traversal.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Page

open Silmaril.Formats Silmaril.Formats.Parquet.Page
open Silmaril.Formats.ThriftCompact

public theorem readHeaderPrefix_stop {limits : HeaderLimits} {window : Bytes} {header : Header}
    {consumed : Nat} (parsed : readHeaderPrefix limits window = .ok (header, consumed)) :
    0 < consumed ∧ consumed ≤ window.length ∧ window.data[consumed - 1]? = some 0 := by
  cases traverse : Traversal.readStruct ⟨window, limits.compact, limits.varintMode⟩ 0 with
  | error e => simp [readHeaderPrefix, traverse, Except.mapError, bind, Except.bind] at parsed
  | ok result =>
    obtain ⟨fields, next⟩ := result
    by_cases invalid : next = 0 ∨ window.length < next
    · simp [readHeaderPrefix, traverse, invalid, Except.mapError, bind, Except.bind] at parsed
    · cases projection : project ⟨⟨window.data.extract 0 next⟩, limits.compact, limits.varintMode⟩ fields with
      | error e => simp [readHeaderPrefix, traverse, invalid, projection, Except.mapError, bind, Except.bind] at parsed
      | ok value =>
        simp [readHeaderPrefix, traverse, invalid, projection, Except.mapError,
          bind, Except.bind, pure, Except.pure] at parsed
        obtain ⟨stop, afterStop, byteAt⟩ := Traversal.readStruct_stop traverse
        have nextEq : next = consumed := parsed.2
        have offsetEq : consumed - 1 = stop := by omega
        exact ⟨by omega, by omega, offsetEq.symm ▸ byteAt⟩

end Silmaril.Proofs.Formats.Parquet.Page
