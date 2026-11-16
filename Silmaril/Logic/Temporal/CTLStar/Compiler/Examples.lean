module

public import Silmaril.Logic.Temporal.CTLStar.Compiler.Thms
public import Silmaril.Logic.Temporal.CTLStar.Examples
public import Silmaril.Logic.Temporal.CTLStar.Terminal.Examples
public import Silmaril.Logic.Temporal.CTLStar.MaximalPath.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.Compiler.Examples

-- Controls use the public correctness theorem without unfolding generated automata.
attribute [local irreducible] compileState compilePathNNF

namespace Source
abbrev terminal := CTLStar.Terminal.Examples.singletonModel
abbrev terminalPath := CTLStar.Terminal.Examples.singletonPath
abbrev edge := CTLStar.Terminal.Examples.edgeModel
abbrev edgePath := CTLStar.Terminal.Examples.edgePath
end Source

/-- Actual emitted scalar syntax preserves weak next at a deadlock. -/
theorem terminal_weakNext :
    ModalMu.Sat (encodeModel Source.terminal)
      (compileState (.existsPath (PathFormula.weakNext (.state .bot)))) := by
  apply (compileState_correct _ _ ModalMu.emptyEnv _).mpr
  exact ⟨Source.terminalPath, rfl, CTLStar.Terminal.Examples.singleton_weakNext_bottom⟩

/-- Strong next cannot manufacture a successor by padding a finite path. -/
theorem terminal_not_strongNext :
    ¬ ModalMu.Sat (encodeModel CTLStar.Examples.terminalModel)
      (compileState (.existsPath (.next .top))) := by
  intro h
  exact CTLStar.Examples.terminal_not_exists_next
    ((compileState_correct _ _ ModalMu.emptyEnv _).mp h)

/-- A path leaf is a recursively compiled state formula, including its quantifier. -/
theorem finite_nested_exists :
    ModalMu.Sat (encodeModel Source.edge)
      (compileState (.existsPath (.state (.existsPath (.next (.state (.atom ()))))))) := by
  apply (compileState_correct _ _ ModalMu.emptyEnv _).mpr
  exact ⟨Source.edgePath, rfl, Source.edgePath, rfl,
    CTLStar.Terminal.Examples.edge_next_atom⟩

/-- Negation of an embedded existential sees the same genuine deadlock. -/
theorem terminal_nested_negation :
    ModalMu.Sat (encodeModel CTLStar.Examples.terminalModel)
      (compileState (.existsPath (.state (.neg (.existsPath (.next .top)))))) := by
  apply (compileState_correct _ _ ModalMu.emptyEnv _).mpr
  exact ⟨CTLStar.Examples.terminalPath, rfl, CTLStar.Examples.terminal_not_exists_next⟩

/-- Derived universal quantification is recursively compiled inside a path leaf. -/
theorem terminal_nested_allPaths :
    ModalMu.Sat (encodeModel Source.terminal)
      (compileState (.existsPath (.state
        (.allPaths (PathFormula.weakNext (.state .bot)))))) := by
  apply (compileState_correct _ _ ModalMu.emptyEnv _).mpr
  refine ⟨Source.terminalPath, rfl, ?_⟩
  apply (StateFormula.allPaths_iff Source.terminal _ ()).mpr
  intro path _
  apply (PathFormula.weakNext_iff Source.terminal _ path 0).mpr
  intro hv
  exact (path.edges 0 hv).elim

/-- The endpoint successor has its own actual zero-edge maximal path. -/
def edgeTerminalPath : Path Source.edge.toModal.accessible :=
  ⟨fun _ => true, some 0,
    fun _ h => by simp only [ValidIndex] at h; omega,
    fun _ _ _ h => Bool.noConfusion h.1⟩

/-- Outer strong next reaches a terminal state where an inner weak-next exists. -/
theorem finite_alternating_next :
    ModalMu.Sat (encodeModel Source.edge)
      (compileState (.existsPath (.next (.state
        (.existsPath (PathFormula.weakNext (.state .bot))))))) := by
  apply (compileState_correct _ _ ModalMu.emptyEnv _).mpr
  refine ⟨Source.edgePath, rfl, ?_, edgeTerminalPath, rfl, ?_⟩
  · change 1 ≤ 1
    omega
  · exact PathFormula.weakNext_at_terminal Source.edge _ edgeTerminalPath rfl

/-- Infinitely many fresh inner witnesses can coexist with one outer spine. -/
theorem loop_nested_requantification :
    ModalMu.Sat (encodeModel CTLStar.Examples.loopModel)
      (compileState (.existsPath (.globally (.state
        (.existsPath (.eventually (.state (.atom ())))))))) :=
  (compileState_correct _ _ ModalMu.emptyEnv _).mpr
    CTLStar.Examples.loop_exists_globally_exists_eventually_write

/-- Flattening the inner choice into one GF path changes the property. -/
theorem loop_not_flat_GF :
    ¬ ModalMu.Sat (encodeModel CTLStar.Examples.loopModel)
      (compileState (.existsPath (.globally (.eventually (.state (.atom ())))))) := by
  intro h
  exact CTLStar.Examples.loop_not_exists_globally_eventually_write
    ((compileState_correct (.existsPath (.globally (.eventually (.state (.atom ())))))
      CTLStar.Examples.loopModel ModalMu.emptyEnv _).mp h)

/-- A real infinite writing path does satisfy the emitted GF formula. -/
theorem writing_GF :
    ModalMu.Sat (encodeModel CTLStar.Examples.writing)
      (compileState (.existsPath (.globally (.eventually (.state (.atom ())))))) :=
  (compileState_correct (.existsPath (.globally (.eventually (.state (.atom ())))))
    CTLStar.Examples.writing ModalMu.emptyEnv _).mpr
    CTLStar.Examples.writing_globally_eventually

abbrev boolSig : CTLStar.Signature := ⟨Bool⟩

/-- One p-only finite branch and one q-only infinite branch. -/
def mixed : CTLStar.Model boolSig :=
  ⟨⟨Option Bool, MaximalPath.Examples.mixed.step (), fun b w => w = some b, none⟩⟩

def choose (b : Bool) : StateFormula boolSig := .existsPath (.next (.state (.atom b)))

/-- Distinct nested state quantifiers may choose distinct successor paths. -/
theorem mixed_nested_choices :
    ModalMu.Sat (encodeModel mixed)
      (compileState (.existsPath (.state (.conj (choose false) (choose true))))) := by
  apply (compileState_correct _ _ ModalMu.emptyEnv _).mpr
  refine ⟨MaximalPath.Examples.finitePath, rfl, ?_, ?_⟩
  · exact ⟨MaximalPath.Examples.finitePath, rfl, by change 1 ≤ 1; omega, rfl⟩
  · exact ⟨MaximalPath.Examples.infinitePath, rfl, trivial, rfl⟩

/-- A single outer path cannot combine the labels of incompatible branches. -/
theorem mixed_not_flat_choice :
    ¬ ModalMu.Sat (encodeModel mixed)
      (compileState (.existsPath (.conj (.next (.state (.atom false)))
        (.next (.state (.atom true)))))) := by
  intro h
  obtain ⟨path, _, hp, hq⟩ := (compileState_correct
    (.existsPath (.conj (.next (.state (.atom false))) (.next (.state (.atom true)))))
    mixed ModalMu.emptyEnv _).mp h
  have hp' : path.state 1 = some false := hp.2
  have hq' : path.state 1 = some true := hq.2
  exact Bool.noConfusion (Option.some.inj (hp'.symm.trans hq'))

/-- Noninjective atom renaming acts on the actual emitted scalar syntax. -/
def collapse : boolSig ⟶ CTLStar.Examples.sig := fun _ => ()

theorem collapse_nested_syntax :
    (compileState (.existsPath (.state (.conj (choose false) (choose true))))).map
      (toMuMap collapse) =
    compileState ((StateFormula.existsPath (.state (.conj (choose false) (choose true)))).map
      collapse) := compileState_map _ collapse

end Silmaril.Logic.Temporal.CTLStar.Compiler.Examples
