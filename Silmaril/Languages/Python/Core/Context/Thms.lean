module

public import Silmaril.Languages.Python.Core.Context.Defs
public import Silmaril.Languages.Python.Core.Thms
import Silmaril.Proofs.Languages.Python.Core.Context.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Context

theorem focus_source (expr : Expr) : (focus expr).expr = expr :=
  Proofs.Languages.Python.Core.Context.focus_source expr

/-- A plugged arithmetic redex is selected with exactly its original context. -/
theorem focus_plug (frames : List Frame) (redex : Redex) :
    focus (plug frames redex.expr) = .redex frames redex :=
  Proofs.Languages.Python.Core.Context.focus_plug frames redex

theorem focus_iff {frames : List Frame} {redex : Redex} {expr : Expr} :
    focus expr = .redex frames redex ↔ plug frames redex.expr = expr :=
  Proofs.Languages.Python.Core.Context.focus_iff

theorem plug_step (frames : List Frame) {expr : Expr} {next : Except Exception Expr}
    (step : expr.Step next) : (plug frames expr).Step (resume frames next) :=
  Proofs.Languages.Python.Core.Context.plug_step frames step

theorem reduces_iff {expr : Expr} {next : Except Exception Expr} : Reduces expr next ↔ expr.Step next :=
  Proofs.Languages.Python.Core.Context.reduces_iff

theorem reduce_iff {expr : Expr} {next : Except Exception Expr} :
    reduce expr = some next ↔ expr.Step next :=
  Proofs.Languages.Python.Core.Context.reduce_iff

theorem reduce_eq_core (expr : Expr) : reduce expr = expr.reduce :=
  Proofs.Languages.Python.Core.Context.reduce_eq_core expr

theorem advance_eq_core (state : State) : advance state = state.advance :=
  Proofs.Languages.Python.Core.Context.advance_eq_core state

theorem advance_iff {source target : State} {label : Option Completion} :
    advance source = some (label, target) ↔ Step source label target :=
  advance_eq_core source ▸ State.advance_iff

end Silmaril.Languages.Python.Core.Context
