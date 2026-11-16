module

public import Silmaril.Elf.Link.Dyn.Libc.Hello.Defs
public import Silmaril.Elf.Link.Dyn.Libc.Thms
public import Silmaril.Elf.Link.Dyn.Program.Examples.Thms
import Silmaril.Proofs.Elf.Link.Dyn.Libc.Hello

/-! # `hello` against the loosest libc specification it needs

`helloGcc_verified` (`Silmaril.Elf.Link.Dyn.Program.Examples`) is proved against the standard
table `Program.lib`. `hello` imports `puts` only, so what it needs of the table is `putsSpec`
(`helloGcc_needs`), and by `Verified.of_needs` it runs correctly against **every** libc
specification above `putsSpec` (`helloGcc_on`): any glibc version, musl, or an interposed library,
as soon as the library meets `puts`'s contract. No re-proof: the statement names exactly the one
contract the binary relies on; the transfer is only as good as the target library's contract for
`puts`. Ported from hiloopai/moria-lean `Moria/Machine/Link/Dyn/Libc/Examples/Hello.lean`
(without `helloGcc_leetcode`, whose leetcode libc stays in moria-lean).

Proofs: `Silmaril.Proofs.Elf.Link.Dyn.Libc.Hello` (standard axioms only).
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Libc

open Silmaril.Elf.Link.Dyn.Program
open Silmaril.Elf.Link.Dyn.Program.Examples

/-- **What `hello` needs**: `puts`. -/
theorem helloGcc_needs : helloGcc.needs lib = putsSpec :=
  Silmaril.Proofs.Elf.Link.Dyn.Libc.Hello.helloGcc_needs

/-- **`hello` runs correctly on every libc specification above `putsSpec`.** -/
theorem helloGcc_on {M : LibcSpec} (hM : putsSpec ≤ M) :
    Verified helloGcc libc ld helloSpec Tier.reliable M.table :=
  Verified.of_needs helloGcc_verified (by rw [helloGcc_needs]; exact hM)

end Silmaril.Elf.Link.Dyn.Libc
