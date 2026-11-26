module

public import Silmaril.Wasm.SSA.MLIRMath.Thms
import Silmaril.Proofs.Wasm.SSA.MLIRMath.Log

@[expose] public section

namespace Silmaril.Wasm.SSA.MLIRMath.Examples

open Silmaril.Numeric.Libm

theorem log_one_exact : Double.log.exact (toF64 0x3ff0000000000000) = some 0 :=
  Proofs.Wasm.SSA.MLIRMath.log_one_exact

/-- An original fixture for
`(module (func (export "fabs") (param f64) (result f64) local.get 0 f64.abs))`. -/
def fabsFixture : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x06, 0x01, 0x60, 0x01, 0x7c, 0x01, 0x7c,
  0x03, 0x02, 0x01, 0x00,
  0x07, 0x08, 0x01, 0x04, 0x66, 0x61, 0x62, 0x73, 0x00, 0x00,
  0x0a, 0x07, 0x01, 0x05, 0x00, 0x20, 0x00, 0x99, 0x0b]⟩

theorem fabs_fixture_checked : WasmExport.checkUnopBytes fabsFixture Double.fabs.name .abs = true :=
  by decide +kernel

-- Keep the binary abstract when applying the theorem to the checked fixture.
attribute [local irreducible] WasmExport.BuildExports in
theorem fabs_fixture_exports : WasmExport.BuildExports fabsFixture Double.fabs.name AbsFNode :=
  absf_build_exports (bytes := fabsFixture) fabs_fixture_checked

end Silmaril.Wasm.SSA.MLIRMath.Examples
