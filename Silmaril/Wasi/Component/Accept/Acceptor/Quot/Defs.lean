module

public import Silmaril.Wasi.Component.Accept.Acceptor.Defs
public import Silmaril.Semantics.Accept.Order.Defs

/-! # Acceptors up to semantic equivalence

The generic order and quotient vocabulary of `Silmaril.Semantics.Accept.Order` applies to
the acceptors through two program equivalences that come from the semantics:

* `ModuleAcceptor.calloutSetoid`: the same acceptor choices (profile, environments, memory,
  imports, width) and callout-equivalent modules (`CalloutEquiv`);
* `ComponentAcceptor.traceSetoid`: the same `accept`, `reject` and mode, and equal named traces
  (`Traces`), possibly over different worlds.

Both respect each acceptor language (`Thms`), so the languages descend to the quotients
(`Silmaril.Accept.LangQuot`). Both are finer than equality of languages
(`Silmaril.Accept.LangEq`): different modules can accept the same bytes by different calls.
`ByteAcceptor.lang` is `Silmaril.Accept.langSum` of the two languages, so a module and a
component in canonical-ABI correspondence are one class of `LangEq ByteAcceptor.lang`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Accept.ModuleAcceptor

/-- The same acceptor choices, and callout-equivalent modules. -/
def CalloutRel (A B : ModuleAcceptor) : Prop :=
  A.profile = B.profile ∧ A.envs = B.envs ∧ A.memIdx = B.memIdx ∧ A.accept = B.accept ∧
    A.reject = B.reject ∧ A.addr = B.addr ∧
    CalloutEquiv A.profile A.envs A.memIdx A.module B.module

/-- **Module acceptors up to callout equivalence.** -/
def calloutSetoid : Setoid ModuleAcceptor where
  r := CalloutRel
  iseqv := {
    refl _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    symm := fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
      refine ⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm, h₅.symm, h₆.symm, ?_⟩
      rw [← h₁, ← h₂, ← h₃]; exact Eq.symm h₇
    trans := fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩ => by
      refine ⟨h₁.trans g₁, h₂.trans g₂, h₃.trans g₃, h₄.trans g₄, h₅.trans g₅, h₆.trans g₆, ?_⟩
      rw [← h₁, ← h₂, ← h₃] at g₇; exact Eq.trans h₇ g₇ }

end Silmaril.Wasm.Game.Accept.ModuleAcceptor

namespace Silmaril.Wasi.Accept.ComponentAcceptor

/-- The same distinguished functions and mode, and equal named traces. -/
def TraceRel (A B : ComponentAcceptor) : Prop :=
  A.accept = B.accept ∧ A.reject = B.reject ∧ A.mode = B.mode ∧ Traces A.model = Traces B.model

/-- **Component acceptors up to equal named traces.** -/
def traceSetoid : Setoid ComponentAcceptor where
  r := TraceRel
  iseqv := {
    refl _ := ⟨rfl, rfl, rfl, rfl⟩
    symm := fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm⟩
    trans := fun ⟨h₁, h₂, h₃, h₄⟩ ⟨g₁, g₂, g₃, g₄⟩ =>
      ⟨h₁.trans g₁, h₂.trans g₂, h₃.trans g₃, h₄.trans g₄⟩ }

end Silmaril.Wasi.Accept.ComponentAcceptor
