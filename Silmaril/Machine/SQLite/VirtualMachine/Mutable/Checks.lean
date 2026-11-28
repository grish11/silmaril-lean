module

import Silmaril.Machine.SQLite.VirtualMachine.Mutable.Thms

namespace Silmaril.Machine.SQLite.VirtualMachine.Mutable

private def config : Configuration :=
  ⟨initial, #[.original (.string8 "λ" 1), .original (.resultRow 1 1), .original (.goto 0)]⟩
private def out := Mutable.run (fun _ _ => none) 5 config

example : config.code[0]? = some (.original (.string8 "λ" 1)) := by decide
example : out.code[0]? = some (.cachedString "λ" 1) := by decide
example : out.code[2]? = some (.original (.goto 0)) := by decide
example : observe out.result = ⟨[[.text "λ"], [.text "λ"]], .exhausted⟩ := by decide

end Silmaril.Machine.SQLite.VirtualMachine.Mutable
