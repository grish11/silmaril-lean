module

public import Silmaril.Courses.Cambridge.L2.Denotation.EffectfulInstitution

/-! # Checked CBV store observations -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.EffectfulDenotation.Examples

def locations : L1.TypeEnv := (∅ : L1.TypeEnv).insert "l" .intref

theorem declared : "l" ∈ locations := by decide

def initialStore : Store := L1.Store.fromList [("l", 0)]

theorem coversInitial : Covers locations initialStore := by
  intro loc present
  simpa [typingEnv, locations, initialStore, L1.Store.fromList, L1.Store.empty,
    Finmap.mem_insert, Finmap.notMem_empty] using present

/-- Slide 138. The body writes 1 after the argument writes 2. -/
def writes : Expr :=
  (RawExpr.app (.lam "x" .unit (.seq (.assign "l" (.int 1)) (.var "x")))
    (.assign "l" (.int 2))).resolve []

def writesTerm : Term locations [] writes .unit :=
  .app (.lam (.seq (.assign declared (.int 1)) (.bvar rfl))) (.assign declared (.int 2))

def writesResult : Config := ⟨.skip, initialStore.insert "l" 1⟩

theorem writes_observes : writesResult ∈ writesTerm.observe .unit initialStore := by
  have first : L1.Store.update initialStore "l" 2 = some (initialStore.insert "l" 2) :=
    L1.Store.update_eq_some _ _ _ (coversInitial _ declared)
  have second : L1.Store.update (initialStore.insert "l" 2) "l" 1 =
      some (initialStore.insert "l" 1) := by
    rw [L1.Store.update_eq_some _ _ _ (Finmap.mem_insert.mpr (Or.inl rfl)), Finmap.insert_insert]
  simp [writesTerm, Term.observe, Term.denote, StateT.run, Bind.bind, Pure.pure,
    StateT.bind, StateT.pure, write, first, second, quoteGround, writesResult,
    Part.ofOption, Part.bind_some, Part.map_some, Denotation.LexicalEnv.lookup,
    Denotation.LexicalEnv.push]

def writesSource : ObservationSource :=
  ⟨locations, writes, .unit, writesTerm, .unit, initialStore, coversInitial⟩

theorem writes_may_return :
    OperationalInstitution.semantics.May writesSource.config (.returned writesResult) :=
  (sat_iff writesSource writesResult).mp writes_observes

/-- A closure saves the integer read at definition time and reads the store
again after both application operands have executed. -/
def capture : Expr :=
  (RawExpr.letE "x" .int (.deref "l")
    (.letE "f" (.arr .unit .int) (.lam "u" .unit (.binary (.var "x") .add (.deref "l")))
      (.app (.seq (.assign "l" (.int 5)) (.var "f"))
        (.assign "l" (.binary (.deref "l") .add (.int 2)))))).resolve []

def captureTerm : Term locations [] capture .int :=
  .letE (.deref declared)
    (.letE (.lam (.add (.bvar rfl) (.deref declared)))
      (.app (.seq (.assign declared (.int 5)) (.bvar rfl))
        (.assign declared (.add (.deref declared) (.int 2)))))

def captureStore : Store := L1.Store.fromList [("l", 3)]

theorem coversCapture : Covers locations captureStore := by
  intro loc present
  simpa [typingEnv, locations, captureStore, L1.Store.fromList, L1.Store.empty,
    Finmap.mem_insert, Finmap.notMem_empty] using present

def captureResult : Config := ⟨.int 10, captureStore.insert "l" 7⟩

theorem capture_observes : captureResult ∈ captureTerm.observe .int captureStore := by
  have initial : L1.Store.lookup captureStore "l" = some 3 := by decide
  have first : L1.Store.update captureStore "l" 5 = some (captureStore.insert "l" 5) :=
    L1.Store.update_eq_some _ _ _ (coversCapture _ declared)
  have second : L1.Store.update (captureStore.insert "l" 5) "l" 7 =
      some (captureStore.insert "l" 7) := by
    rw [L1.Store.update_eq_some _ _ _ (Finmap.mem_insert.mpr (Or.inl rfl)), Finmap.insert_insert]
  simp [captureTerm, Term.observe, Term.denote, StateT.run, Bind.bind, Pure.pure,
    StateT.bind, StateT.pure, read, write, initial, first, second, quoteGround, captureResult,
    Part.ofOption, Part.bind_some, Part.map_some, Denotation.LexicalEnv.lookup,
    Denotation.LexicalEnv.push]

theorem capture_returns : Steps ⟨capture, captureStore⟩ captureResult :=
  ((captureTerm.adequate .int coversCapture _).mp capture_observes).1

end Silmaril.Courses.Cambridge.L2.EffectfulDenotation.Examples
