module

public import Silmaril.Elf.Link.Dyn.Libc.Defs

/-! # The libc specification `hello` needs

`putsSpec`: the one-symbol specification of `puts` (`Program.putsStep`, the contract of the
standard table `Program.lib`). Ported from hiloopai/moria-lean
`Moria/Machine/Link/Dyn/Libc/Leetcode/Defs.lean` (`putsSpec` only; the leetcode libc stays there).
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Libc

open Silmaril.Elf.Link.DynElf

/-- `puts` (`Program.putsStep`), the specification `hello` needs. -/
def putsSpec : LibcSpec := ⟨[(nm "puts", fun c => Program.putsStep c.S c.W)]⟩

end Silmaril.Elf.Link.Dyn.Libc
