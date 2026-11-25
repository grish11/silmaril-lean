module

public import Silmaril.Languages.Starlark.Modules.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Modules

open Functions
open Lists

inductive Executes (program : Program) (host : Catalog) : State → Command → Result Unit → Prop where
  | exec {s : State} {code : TopCode} {out : Outcome Iteration.Flow} :
      Exec program (List.range program.size) s code.body out →
      Executes program host s (.exec code) (afterCode out)
  | load {s : State} {label : String} {imports : List Import} :
      Executes program host s (.load label imports) (loadFrom host label imports s)

inductive Runs (program : Program) (host : Catalog) : State → List Command → Result Unit → Prop where
  | done {s : State} : Runs program host s [] (.ok () s)
  | step {s t : State} {first : Command} {rest : List Command} {out : Result Unit} :
      Executes program host s first (.ok () t) → Runs program host t rest out →
      Runs program host s (first :: rest) out
  | failed {s t : State} {first : Command} {rest : List Command} {error : Error} :
      Executes program host s first (.error error t) →
      Runs program host s (first :: rest) (.error error t)

inductive Initializes (program : Program) (host : Catalog) (source : Source) (caller : State) :
    Result Published → Prop where
  | reject {error : Error} : validateSource program source = .error error →
      Initializes program host source caller (.error error caller)
  | run {out : Result Unit} : validateSource program source = .ok () →
      Runs program host (enter source caller) source.commands out →
      Initializes program host source caller (finish source caller out)

end Silmaril.Languages.Starlark.Modules
