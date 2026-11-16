module

public import Silmaril.Machine.Abi.Conformance.LeafArith.Defs
public import Silmaril.Machine.Abi.Conformance.Thms
import Silmaril.Proofs.Machine.Abi.Conformance.LeafArith

/-! # ABI conformance of rung 01: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.LeafArith`:

* `clamp_conforms`, `sat_conforms`: gcc -O2 `clamp_i32` and `sat_add_u32` conform to the
  System V AMD64 psABI (INTEGER fragment, `sysvInt`) as `arith.h` declares them, with their
  source functions as C specs, no stack frame, no memory written, on the open machine, in both
  modes;
* `clamp_rejects_first`: the statement discriminates: `clamp_i32` does not conform with the
  spec "returns its first argument";
* `coverage_check`, `header_sat`: `arith.h` (with `rt.h`) is accounted for: the two functions
  are claimed and conform, every other declaration is excluded with its reason.

OPEN (`Task`): the first-return rows of `gcd_u32` and `bswap32_manual`, whose block
certificates are proved (`Silmaril.X86.Ladder.LeafArith`) but not in first-return form.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.LeafArith

open Silmaril.X86 (Open.isa)

theorem clamp_conforms (mode : Mode) :
    Conforms sysvInt Open.isa mode hdr "clamp_i32" clampProto clampCode 0 clampS :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.clamp_conforms mode

theorem sat_conforms (mode : Mode) :
    Conforms sysvInt Open.isa mode hdr "sat_add_u32" satProto satCode 0 satS :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.sat_conforms mode

theorem clamp_rejects_first (mode : Mode) :
    ¬ Conforms sysvInt Open.isa mode hdr "clamp_i32" clampProto clampCode 0 clampFirstS :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.clamp_rejects_first mode

theorem coverage_check : coverage.check sysvInt hdr = true :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.coverage_check

theorem header_sat : HeaderSat sysvInt Open.isa hdr coverage impl :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.header_sat

end Silmaril.Machine.Abi.Conformance.LeafArith

end
