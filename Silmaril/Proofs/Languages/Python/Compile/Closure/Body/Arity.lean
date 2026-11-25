module

public import Silmaril.Languages.Python.Compile.Closure.Body.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.Closure.Body

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure.Body

theorem arguments_length {scope : Source.Scope} {sources targets}
    (translated : ArgumentsTranslation scope sources targets) : targets.length = sources.length :=
  match translated with
  | .nil => rfl
  | .cons _ rest => congrArg Nat.succ (arguments_length rest)

theorem tagged_arguments_length {scope : Source.Scope} {sources targets}
    (translated : TaggedArgumentsTranslation scope sources targets) : targets.length = sources.length :=
  match translated with
  | .nil => rfl
  | .cons _ rest => congrArg Nat.succ (tagged_arguments_length rest)

end Silmaril.Proofs.Languages.Python.Compile.Closure.Body
