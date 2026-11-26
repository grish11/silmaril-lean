module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Defs
public import Silmaril.SSA.PEG.Simple.Structured.Thms
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Nested.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer inner : List (Ty Data)} {result : Ty Data}
variable {form : Form P outer inner result}
variable {g : Graph P outer [result] form.size form.size}

theorem Certificate.compile_eq [DecidableEq Data] (cert : Certificate form g) :
    form.compile = g :=
  Proofs.compile_eq cert

theorem Certificate.demandWellFounded [DecidableEq Data] (cert : Certificate form g) :
    WellFounded g.Demand :=
  cert.compile_eq ▸ Structured.translate_demandWellFounded form.source form.negate

/-- A successful bounded execution executes the emitted SIMPLE program. -/
theorem Form.runFuel_returns (form : Form P outer inner result)
    (m : Interpretation.{u,v,w} P) (outerFuel innerFuel : Nat)
    (input : Tuple m.Value outer) {value : m.Value result}
    (success : form.runFuel m outerFuel innerFuel input = some value) :
    form.source.Returns m input value :=
  Proofs.runFuel_returns form outerFuel innerFuel input success

/-- A defined outer eval recovers a finite outer trace. Each continuing
step contains a successful invocation of the child on the captured store. -/
theorem Certificate.trace_of_defined [DecidableEq Data] (cert : Certificate form g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value outer) (total : form.Total m)
    (neg : ∀ b : Bool, m.run form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index form.size) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) i = .cons (some value) .nil) :
    ∃ k final, WhileTrace m form.outerGuard form.body k input final ∧
      final.get form.returnSlot = value :=
  Proofs.trace_of_defined cert input total neg cert.demandWellFounded i defined

/-- The nested reverter preserves exactly the defined return under the
guard, child termination, commit and Boolean negation premises. -/
theorem Certificate.returns_iff_observe [DecidableEq Data] (cert : Certificate form g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value outer) (total : form.Total m)
    (neg : ∀ b : Bool, m.run form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index form.size) (value : m.Value result) :
    cert.revert.Returns m input value ↔
      g.observe m (g.denote m input cert.demandWellFounded) i = .cons (some value) .nil := by
  constructor
  · intro returned
    have eq := cert.compile_eq
    subst g
    exact Structured.translate_returns form.source form.negate m input neg returned i
  · intro defined
    obtain ⟨_, final, trace, returned⟩ := cert.trace_of_defined m input total neg i defined
    exact ⟨final, trace.exec, returned⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Nested
