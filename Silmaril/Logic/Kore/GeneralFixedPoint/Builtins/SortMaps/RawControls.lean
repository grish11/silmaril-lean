module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Raw
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.PopulatedControls

@[expose] public section
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.RawControls
open PopulatedControls

/-- Closed actual hook/literal term, called through a real zero-argument alias.
Alias module index 0 is required by the actual generated literal lookup. -/
def hookRaw : RawPattern :=
  .app "notBool" [.app "eqInt" [.domainValue "SortInt" "0", .domainValue "SortInt" "0"]]

def closedAlias : Alias where
  symbol := ⟨"zeroIsNotZero", [], "SortBool"⟩
  parameters := []
  body := hookRaw
  moduleIndex := 0

def aliasRaw : RawPattern := .app "zeroIsNotZero" []

/-- These are actual syntactic renaming calculations. Checker acceptance is
independently computed below, not inferred from these equalities. -/
example : renameRaw renameSort id 8 hookRaw = some hookRaw := rfl
example : renameRaw renameSort id 8 aliasRaw = some aliasRaw := rfl

abbrev sourceCheck :=
  @Checking.elaborate source.bindings source.scope [closedAlias] source.literals
    source.literalPrefix 0 12 [] [] "SortBool" aliasRaw
abbrev targetCheck :=
  @Checking.elaborate target.bindings target.scope [closedAlias] target.literals
    target.literalPrefix 0 12 [] [] "SortBool" aliasRaw

theorem source_accepts : sourceCheck.isSome = true := by decide +kernel
theorem target_accepts : targetCheck.isSome = true := by decide +kernel

def sourceTyped := sourceCheck.get source_accepts
def targetTyped := targetCheck.get target_accepts

theorem source_admitted : sourceTyped.admissible = true := by decide +kernel
theorem target_admitted : targetTyped.admissible = true := by decide +kernel

theorem option_eq_some_get {α : Type} (o : Option α) (h : o.isSome = true) :
    o = some (o.get h) := by
  cases o <;> simp_all

def sourceReceipt : @CheckedSentence source.bindings source.scope source.literals source.literalPrefix where
  aliases := [closedAlias]
  moduleIndex := 0
  fuel := 12
  sets := []
  objects := []
  sort := "SortBool"
  raw := aliasRaw
  typed := sourceTyped
  accepted := option_eq_some_get sourceCheck source_accepts
  admitted := source_admitted

def targetReceipt : @CheckedSentence target.bindings target.scope target.literals target.literalPrefix where
  aliases := [closedAlias]
  moduleIndex := 0
  fuel := 12
  sets := []
  objects := []
  sort := "SortBool"
  raw := aliasRaw
  typed := targetTyped
  accepted := option_eq_some_get targetCheck target_accepts
  admitted := target_admitted

/-- Exact actual alias lookup and module-index controls: changing the alias
name or exhausting fuel must not silently create a receipt. -/
example : (@Checking.elaborate source.bindings source.scope [closedAlias]
    source.literals source.literalPrefix 0 0 [] [] "SortBool" aliasRaw).isSome = false := rfl
example : (@Checking.elaborate source.bindings source.scope [] source.literals
    source.literalPrefix 0 12 [] [] "SortBool" aliasRaw).isSome = false := by decide +kernel

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.RawControls
