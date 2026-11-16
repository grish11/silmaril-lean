module

public import Silmaril.Elf.Link.Dyn.Libc.Hello.Defs
public import Silmaril.Elf.Link.Dyn.Program.Examples.HelloGccBin

/-! # Proofs of `Silmaril.Elf.Link.Dyn.Libc.Hello`

Ported from hiloopai/moria-lean `Moria/Machine/Link/Dyn/Libc/Examples/Hello.lean`
(`lib_puts`, `helloGcc_needs`). -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Link.Dyn.Libc.Hello

open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Libc
open Silmaril.Elf.Link.Dyn.Program
open Silmaril.Elf.Link.Dyn.Program.Examples

theorem lib_puts (S : Std) (prog : List Silmaril.X86.Byte) (W : Proc.World) :
    Streams.namedOf (lib S prog W) (nm "puts") = putsStep S W := by
  simp [Streams.namedOf, lib]

theorem helloGcc_needs : helloGcc.needs lib = putsSpec := by
  have h : helloGcc.imports.map (·.name) = [nm "puts"] := rfl
  simp only [Bin.needs, LibcSpec.ofTable, h, List.map_cons, List.map_nil, putsSpec,
    LibcSpec.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  funext c
  exact lib_puts c.S c.prog c.W

end Silmaril.Proofs.Elf.Link.Dyn.Libc.Hello
