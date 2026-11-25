module

public import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs
import Silmaril.Proofs.ProofFormats.TLA.SurfaceSExp.RoundTrip

public section

namespace Silmaril.ProofFormats.TLA.SurfaceSExp

open Silmaril.Logic.Temporal.TLA.Surface

theorem decodeModule_encodeModule (value : Module) :
    decodeModule (encodeModule value) = .ok value :=
  Proofs.ProofFormats.TLA.SurfaceSExp.decodeModule_encodeModule value

theorem decodeExpr_encodeExpr (value : Expr) :
    decodeExpr (encodeExpr value) = .ok value :=
  Proofs.ProofFormats.TLA.SurfaceSExp.decodeExpr_encodeExpr value

/-- A successfully decoded module tree is in the canonical image of the encoder. -/
theorem encodeModule_of_decodeModule {tree : Tree} {value : Module}
    (accepted : decodeModule tree = .ok value) : encodeModule value = tree :=
  Proofs.ProofFormats.TLA.SurfaceSExp.encodeModule_of_decodeModule accepted

/-- A successfully decoded expression tree is in the canonical image of the encoder. -/
theorem encodeExpr_of_decodeExpr {tree : Tree} {value : Expr}
    (accepted : decodeExpr tree = .ok value) : encodeExpr value = tree :=
  Proofs.ProofFormats.TLA.SurfaceSExp.encodeExpr_of_decodeExpr accepted

theorem decodeModuleText_encodeModuleText (value : Module) :
    decodeModuleText (encodeModuleText value) = .ok value :=
  Proofs.ProofFormats.TLA.SurfaceSExp.decodeModuleText_encodeModuleText value

theorem decodeExprText_encodeExprText (value : Expr) :
    decodeExprText (encodeExprText value) = .ok value :=
  Proofs.ProofFormats.TLA.SurfaceSExp.decodeExprText_encodeExprText value

theorem decodeModuleBytes_encodeModuleBytes (value : Module) :
    decodeModuleBytes (encodeModuleBytes value) = .ok value :=
  Proofs.ProofFormats.TLA.SurfaceSExp.decodeModuleBytes_encodeModuleBytes value

theorem decodeExprBytes_encodeExprBytes (value : Expr) :
    decodeExprBytes (encodeExprBytes value) = .ok value :=
  Proofs.ProofFormats.TLA.SurfaceSExp.decodeExprBytes_encodeExprBytes value

end Silmaril.ProofFormats.TLA.SurfaceSExp
