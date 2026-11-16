module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Naturality.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.AliasValidity.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.LiteralOperations.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

/-- The existing fuel-bounded checker applied to a source package. -/
abbrev elaboratePackage (A : Package) (mi fuel : Nat) (sets objects : Names)
    (s : String) (raw : RawPattern) : Option (@Pattern A.base.scope sets objects s) :=
  @Checking.elaborate A.base.bindings A.base.scope A.aliases A.base.literals
    A.base.literalPrefix mi fuel sets objects s raw

/-- The exact forward checker equation at one fuel. This is the induction
hypothesis used at a strictly smaller fuel in recursive constructors. -/
def FuelTransport {A B : Package} (f : Step A B) (fuel : Nat) : Prop :=
  ∀ (mi : Nat) (sets objects : Names) (s : String) (raw : RawPattern)
    (p : @Pattern A.base.scope sets objects s),
    elaboratePackage A mi fuel sets objects s raw = some p →
    elaboratePackage B mi fuel (mapNames f.semantic.native.sorts sets)
      (mapNames f.semantic.native.sorts objects) (f.semantic.native.sorts s)
      (Surface.raw f.semantic.native.sorts f.names raw) = some (reindexPattern f p)

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
