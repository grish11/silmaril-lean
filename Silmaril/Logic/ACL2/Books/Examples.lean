module

public import Silmaril.Logic.ACL2.Books.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.Examples

def firstName : Name := ⟨"ACL2", "SILMARIL-FIRST"⟩
def firstConsName : Name := ⟨"ACL2", "SILMARIL-FIRST-OF-CONS"⟩
def firstSingletonName : Name := ⟨"ACL2", "SILMARIL-FIRST-OF-SINGLETON"⟩

def firstBody : Term World.initial.signature 1 := .car (.var 0)

theorem firstFresh : World.initial.Fresh firstName := ⟨rfl, rfl⟩

def definedWorld : World := World.initial.define firstFresh firstBody

def firstSymbol : definedWorld.signature.Symbol 1 :=
  World.initial.signature.addSymbol firstName 1

def first {n : Nat} (x : Term definedWorld.signature n) : Term definedWorld.signature n :=
  .app firstSymbol (fun _ => x)

def firstCons : Sentence definedWorld.signature :=
  .eq (first (.cons (.var (0 : Fin 2)) (.var 1))) (.var 0)

theorem firstDefinition :
    definitionEquation firstSymbol (firstBody.map (Signature.addInclusion firstFresh.1 1)) ∈
      definedWorld.theory :=
  Or.inl ⟨1, firstSymbol, _, World.initial.presentation.define_body_new firstFresh.1 firstBody, rfl⟩

theorem firstConsProof : definedWorld.Provable firstCons := by
  have unfoldFirst := Derives.subst (fun _ => Term.cons (.var (0 : Fin 2)) (.var 1))
    (Derives.hyp firstDefinition)
  exact Derives.trans unfoldFirst (.carCons _ _)

def provedWorld : World := definedWorld.addTheorem firstConsName ⟨rfl, rfl⟩ firstCons firstConsProof

def firstSingleton : Sentence provedWorld.signature :=
  .eq (first (.cons (.var (0 : Fin 1)) .nil)) (.var 0)

theorem firstSingletonProof : provedWorld.Provable firstSingleton := by
  let args : Fin 2 → Term provedWorld.signature 1 := fun i => if i = 0 then .var 0 else .nil
  exact Derives.subst args
    (Derives.hyp (Or.inr ⟨firstConsName, rfl⟩) : provedWorld.Provable firstCons)

def exampleWorld : World := provedWorld.addTheorem firstSingletonName ⟨rfl, rfl⟩ firstSingleton firstSingletonProof

def definitionsBook : Book World.initial definedWorld :=
  .cons (.defun firstFresh firstBody) (.nil _)

def theoremsBook : Book definedWorld exampleWorld :=
  .cons (.defthm ⟨rfl, rfl⟩ firstCons firstConsProof)
    (.cons (.defthm ⟨rfl, rfl⟩ firstSingleton firstSingletonProof) (.nil _))

/-- Load a definition book, then include a theorem book that depends on it. -/
def exampleBook : Book World.initial exampleWorld := definitionsBook.includeBook theoremsBook

theorem exampleWorld_checked : exampleWorld.Checked :=
  exampleBook.checked (World.checked_bare _)

theorem exampleWorld_valid : exampleWorld.Valid :=
  exampleBook.valid (World.valid_bare _)

end Silmaril.Logic.ACL2.Examples
