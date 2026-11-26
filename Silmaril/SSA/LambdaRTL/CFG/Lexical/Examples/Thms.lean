module

public import Silmaril.SSA.LambdaRTL.CFG.Version.Flat.Thms

/-! Both branches overwrite a register that the join reads. The versioned
graph carries its new value to the join as part of the block argument. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.LexicalExamples

private inductive Value
  | word (value : Nat)
  | pair (left right : Value)
  | inl (value : Value)
  | inr (value : Value)
  deriving DecidableEq

private def model : Model Bool Option Value where
  unit := .word 0
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair a b => some (a, b)
    | _ => none
  split
    | .inl a => some (.inl a)
    | .inr a => some (.inr a)
    | _ => none
  app right
    | .word n => some (.word (n + if right then 10 else 1))
    | _ => none
  abort _ := none

private theorem pairLaw : model.PairLawful := ⟨fun _ _ => rfl⟩

private def source : CFG Nat Nat Bool :=
  ⟨.term (.case (.val (.var 0)) 1 (.br 10 (.var 1)) 2 (.br 20 (.var 2))),
    [(10, ⟨3, .let1 4 (.app false (.var 3)) (.term (.br 30 .unit))⟩),
     (20, ⟨3, .let1 4 (.app true (.var 3)) (.term (.br 30 .unit))⟩),
     (30, ⟨5, .term (.br 99 (.var 4))⟩)]⟩

private abbrev Register := Nat × Nat

private def packLiveIn (arg : Val Register) (reg : Register) : Val Register :=
  .pair arg (.pair (.var reg) .unit)

private def arm (right : Bool) : Block Register Nat Bool :=
  ⟨(3, 1), .let2 (3, 2) (3, 3) (.val (.var (3, 1))) <|
    .let2 (4, 4) (4, 5) (.val (.var (3, 3))) <|
    .let1 (4, 6) (.app right (.var (3, 2))) <|
    .term (.br 30 (packLiveIn .unit (4, 6)))⟩

private def expected : CFG Register Nat Bool :=
  ⟨.term (.case (.val (.var (0, 0)))
      (1, 1) (.br 10 (packLiveIn (.var (1, 1)) (4, 0)))
      (2, 1) (.br 20 (packLiveIn (.var (2, 1)) (4, 0)))),
    [(10, arm false), (20, arm true),
     (30, ⟨(5, 1), .let2 (5, 2) (5, 3) (.val (.var (5, 1))) <|
        .let2 (4, 4) (4, 5) (.val (.var (5, 3))) <|
        .term (.br 99 (.var (4, 4)))⟩)]⟩

-- The generator produces the same three blocks, with the live-in explicitly
-- packed on both incoming edges to the join.
example : source.versioned = expected := by decide

private def input (test : Value) (reg : Nat) : Value :=
  if reg = 0 then test else .word 7

private def versionInput (test : Value) : Register → Value :=
  fun reg => if reg.2 = 0 then input test reg.1 else .word 0

example : source.versioned.toRegion.IsSSA (Version.initCtx source.toRegion) :=
  versioned_isSSA source

-- Mutable execution carries the new value, whereas the same graph read
-- lexically still sees the input value of register 4 at the join.
example : obs <$> source.run model (input (.inl (.word 11))) = some (99, .word 12) := by decide
example : source.runSSA model (input (.inl (.word 11))) = some (99, .word 7) := by decide

-- Versioning makes the two flat readings agree on each arm's distinct result.
example : source.versioned.runSSA model (versionInput (.inl (.word 11))) = some (99, .word 12) := by
  decide

example : source.versioned.runSSA model (versionInput (.inr (.word 11))) = some (99, .word 21) := by
  decide

example :
    source.versioned.runSSA model (versionInput (.inr (.word 11))) =
      obs <$> source.run model (input (.inr (.word 11))) := by
  rw [versioned_runSSA source model pairLaw]
  rfl

example : source.versioned.runSSA model (versionInput (.word 11)) = none := by decide

end Silmaril.SSA.LambdaRTL.CFG.LexicalExamples
