module

import Silmaril.SSA.Isotope.LetParIter.Thms

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Parallel (Derivation)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (TypeModel TyDen InstructionModel CtxDen BoundDen)

namespace LetParIterTests

open scoped LetParIter

abbrev Obj := Ty Empty

inductive Instr where
  | tick

instance : HasTy Instr Obj := ⟨fun _ => unit, fun _ => unit⟩
instance : HasEff Instr (Bool × Bool) := ⟨fun _ => (true, false)⟩

abbrev Γ : Ctx Empty Obj := .nil
abbrev U : Obj := unit

def native : LetIter.LocallyNameless.Tm Empty Instr 0 := .iter .unit (.inl (.bv 0))

def nativeTyped : LetIter.LocallyNameless.Derivation Instr Γ .nil native U :=
  .iter .unit (.inl .bv)

example : LetParIter.toLetIter? (LetParIter.embed native) = some native :=
  LetParIter.toLetIter?_embed native

example : Derivation Instr Γ .nil (LetParIter.embed native) U :=
  LetParIter.derivation nativeTyped

def nativeWithEta : LetIter.LocallyNameless.Derivation Instr Γ .nil
    (.let₁ native (.bv 0)) U :=
  .let₁ nativeTyped .bv

-- A native equation survives at its original exact typing endpoints.
example : LetParIter.Equiv (⊥ : Bool × Bool) Γ
    (LetParIter.derivation nativeWithEta) (LetParIter.derivation nativeTyped) :=
  .native nativeWithEta nativeTyped ⟨.letEta (LetParIter.nativeTyping nativeTyped)⟩

def unitBranch : Derivation Instr Γ (.snoc .nil U) (.bv 0 : LetParIter.Tm Empty Instr 1) U :=
  .bv

def tickBranch : Derivation Instr Γ (.snoc .nil U) (.op .tick .unit : LetParIter.Tm Empty Instr 1) U :=
  .op .unit

def branches := (.bv 0 : LetParIter.Tm Empty Instr 1) || .op .tick .unit

example : Derivation Instr Γ (.snoc .nil U) branches (product U U) :=
  .par unitBranch tickBranch

example : LetParIter.toLetIter? branches = none := rfl

theorem loopSwap :
    LetParIter.Equiv (⊥ : Bool × Bool) Γ
      (.iter (h := rfl) .unit
        (.inl (h := LetParIter.hasCase) (LetParIter.Typing.swap (.par unitBranch tickBranch))))
      (.iter (h := rfl) .unit (.inl (h := LetParIter.hasCase) (.par tickBranch unitBranch))) :=
  .iter (.refl .unit) (.inl (.swap unitBranch tickBranch))

-- Renaming and simultaneous substitution reach under the loop binder and both branches.
example := LetParIter.Equiv.rename (BoundCtx.Renaming.succ .nil U) loopSwap

theorem swapOpen :
    LetParIter.Equiv (⊥ : Bool × Bool) Γ (LetParIter.Typing.swap (.par unitBranch tickBranch))
      (.par tickBranch unitBranch) :=
  .swap unitBranch tickBranch

def substituteUnit :
    LetParIter.Subst (Γ := Γ) (.snoc .nil U) .nil (fun _ => (.unit : LetParIter.Tm Empty Instr 0)) :=
  fun i => Fin.cases .unit (fun j => Fin.elim0 j) i

example := LetParIter.Equiv.bsubst substituteUnit (fun _ => .unit) swapOpen

def openLoop : LetParIter.Tm Empty Instr 2 :=
  .iter rfl (.bv 0) (.inl LetParIter.hasCase (.par (.bv 0) (.par (.bv 1) (.bv 2))))

def replaceAmbient : Fin 2 → LetParIter.Tm Empty Instr 1 :=
  Fin.cases .unit (fun _ => .bv 0)

-- The loop variable stays at zero, while the replacement mentioning an ambient
-- variable is lifted past the binder.
example : openLoop.bsubst replaceAmbient =
    .iter rfl .unit (.inl LetParIter.hasCase (.par (.bv 0) (.par .unit (.bv 1)))) := rfl

variable [TypeModel.{0, 0} Obj]
variable {m : Type → Type} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]
variable [InstructionModel Instr Obj (Bool × Bool) m]

example (P : Elgot.ParallelPairing m) (γ : CtxDen Γ) (ρ : BoundDen (.nil : BoundCtx Obj 0)) :=
  LetParIter.interpret_sound P loopSwap γ ρ

end LetParIterTests
