module

public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Defs
public import Silmaril.Proofs.Logic.Smt.Uflia.SurfaceSemantics

/-! Independent source evaluation and full successful-decoding preservation for
the currently admitted QF-UFLIA frontend. Fuel induction covers arbitrary local
scopes; accepted formulas and assertion lists preserve source truth in one
coherent global model. The adjacent README records the exact boundary. -/
