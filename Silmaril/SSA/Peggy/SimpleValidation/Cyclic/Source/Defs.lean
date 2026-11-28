module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Defs

/-! # Checked optimization of a top-level SIMPLE while

Compile the designated return and the typed loop store using the
single-loop frontend. Replay the cyclic rewrite and use its redirect
map on that same boundary. An eliminated self-feeding slot can read
its initial parameter directly, while the emitted SIMPLE keeps that
value in the store by an identity update.
-/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source

open PEG PEG.Simple PEG.Simple.Revert.While
open RVSDG (Port)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data}

/-- Translate all typed boundary references through the replay's row
compaction. The region checker will check every proposed slot and wire. -/
def descriptor (p : WhileProgram P params result) (negate : P [.bool] .bool)
    (rewrite : Rewrite (n := p.layout.tail.length) (p.translate negate)) :
    Region.Descriptor rewrite.matched.extract :=
  let ref {t : Ty Data} (port : Port p.layout t) := rewrite.matched.redirect (numberPort port)
  let slots := ports params
  { theta := slots.map fun _ p' => ref (p.carriedPort p')
    initial := slots.map fun _ p' => ref (p.paramRef p')
    next := slots.map fun _ p' => ref (p.localRef (p.core.refs.get (.tail p')))
    guard := ref (p.localRef (p.core.refs.get .head))
    negated := ref (.tail (.tail .head))
    negate
    pass := ref p.passPort
    returnSlot := p.retvar }

structure Accepted (p : WhileProgram P params result) (negate : P [.bool] .bool) where
  cyclic : Cyclic.Accepted (n := p.layout.tail.length) (p.translate negate) true
  negate_eq : cyclic.reversion.descriptor.negate = negate

variable {p : WhileProgram P params result} {negate : P [.bool] .bool}

def Accepted.output (a : Accepted p negate) : Program P true params result :=
  a.cyclic.output

/-- Check one discovered feedback rewrite, then schedule the redirected
compiler boundary with the invariant-slot case enabled. -/
def optimize [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (p : WhileProgram P params result) (negate : P [.bool] .bool) :
    Except Rejection (Accepted p negate) := do
  let graph := p.translate negate
  if ranked : p.rank.check graph = true then
    let some rewrite := findRewrite (n := p.layout.tail.length) graph
      | .error .noCheckedRewrite
    let proposed := descriptor p negate rewrite
    let some checked := Region.checkScheduledWith rewrite.matched.extract proposed rewrite.targetRank true
      | .error .reversion
    return ⟨⟨p.rank, ranked, rewrite, checked.val⟩, congrArg Region.Descriptor.negate checked.property⟩
  else .error .sourceRank

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source
