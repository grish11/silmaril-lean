module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Boundary.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Join.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches)
open Region.Paper (linkedJoin)
open LetCase.Structural.Finite (Shape)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private abbrev input : Shape := .unit
private abbrev bit : Shape := .sum .unit .unit

private instance : LetCase.Structural.Finite.Signature Unit where
  source _ := input
  target _ := bit

private abbrev β : BoundCtx (Ty Empty) 1 := .snoc .nil input.ty

private def entry : Region Unit :=
  .case (.op () (.var 0)) (.br 0 (.var 0)) (.br 0 .unit)

private theorem entryGuarded : ValueBranches [input.ty] entry [input.ty] :=
  .case (.op (.var (i := 0) rfl)) (.br rfl (.var rfl)) (.br rfl .unit)

private def block : Region Unit := .br 0 (.var 0)

private theorem blockGuarded : ValueBranches [input.ty, input.ty] block [input.ty] := .br rfl (.var rfl)

private theorem equation :
    Region.Paper.Eqv [input.ty] (.cfg entry 1 fun _ => .br 1 (.var 0)) entry [input.ty] :=
  linkedJoin entryGuarded blockGuarded

-- Independent native constructors, a real effectful case, and an outward local row.
private def withJoin : Endpoint Unit β input.ty :=
  ⟨.cfg entry 1 (fun _ => .br 1 (.var 0)), equation.typed.1,
    .join (.case _ (.br _) (.br _)) (.br _)⟩

private def withoutJoin : Endpoint Unit β input.ty :=
  ⟨entry, entryGuarded.hasType, .case _ (.br _) (.br _)⟩

example : withJoin.code.toSSA 0 = withJoin.region :=
  withJoin.code_exact

-- Replay uses a native region equation at the original endpoints,
-- and reflection yields an equation of the independently compiled terms.
example : LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ β
    withJoin.compile.1 withoutJoin.compile.1 input.ty :=
  (withJoin.valid_iff_compiled (.snoc .nil input) withoutJoin).mp
    (Endpoint.joined_sound (p := withJoin) (q := withoutJoin) (.paper equation))

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
