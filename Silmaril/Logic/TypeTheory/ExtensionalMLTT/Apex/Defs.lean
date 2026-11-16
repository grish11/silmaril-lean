module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution
public import Mathlib.CategoryTheory.Limits.Cones

@[expose] public section

/-!
# Finite MLTT stages and the full-universe apex

The existing finite stages have small sentence types. `Apex.Sentence` lifts
those types to the same Lean universe as the full institution. Models and
satisfaction are unchanged. Full hierarchies restrict to each finite stage.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.SetTheory

universe u

/-- Forget the hierarchy laws above a finite number of available levels. -/
def SetHierarchy.toFiniteTower (T : SetHierarchy.{u}) (n : ℕ) : FiniteTower.{u} n where
  U := T.U
  isGrothendieck i _ := T.isGrothendieck i
  mem_succ i _ := T.mem_succ i

namespace Apex

/-- A finite sentence in the full institution's sentence universe. -/
abbrev Sentence (n : ℕ) := ULift.{u + 1} (Finite.Sentence n)

/-- The finite-stage room with a canonical sentence-universe lift. -/
def finiteRoom (n : ℕ) : Room.{u + 1, u + 1, u + 1} where
  Sen := Sentence.{u} n
  Mod := (Finite.room.{u} n).Mod
  Sat T j := (Finite.room n).Sat T j.down

/-- The lifted finite-stage institution. -/
def finiteInst (n : ℕ) : Discrete Unit ⥤ Room.{u + 1, u + 1, u + 1} :=
  Discrete.functor fun _ => finiteRoom.{u} n

/-- The bundled lifted finite stage, preserving the original finite API. -/
def finiteBundled (n : ℕ) : Inst.{0, 0, u + 1, u + 1, u + 1} where
  Sign := Discrete Unit
  I := finiteInst.{u} n

/-- Include a lifted finite sentence into a later finite stage. -/
def includeSentence {n m : ℕ} (h : n ≤ m) (j : Sentence.{u} n) : Sentence.{u} m :=
  ULift.up (Finite.includeSentence h j.down)

/-- Lift the original finite-stage corridor without changing models. -/
def inclusionCorridor {n m : ℕ} (h : n ≤ m) : finiteRoom.{u} n ⟶ finiteRoom.{u} m where
  sen := includeSentence h
  mod := Finite.modelReduct h
  sat _ _ := Iff.rfl

/-- The finite-stage inclusion in the full institution's sentence universe. -/
def inclusion {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom (finiteBundled.{u} n) (finiteBundled.{u} m) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => inclusionCorridor h

/-- The lifted inclusion adding one available universe level. -/
def successor (n : ℕ) : Inst.CoHom (finiteBundled.{u} n) (finiteBundled.{u} (n + 1)) :=
  inclusion (Nat.le_succ n)

/-- Forget a finite sentence's bound while preserving its judgment. -/
def toFullSentence {n : ℕ} (j : Sentence.{u} n) : Institution.Sentence.{u} :=
  ULift.up j.down.val

/-- Full models reduce to finite models by retaining their level lookup. -/
def fullModelReduct (n : ℕ) :
    Discrete SetHierarchy.{u} ⥤ Discrete (FiniteTower.{u} n) :=
  Discrete.functor fun T => Discrete.mk (T.toFiniteTower n)

/-- A finite judgment has the same satisfaction in a full model and its reduct. -/
def toFullCorridor (n : ℕ) : finiteRoom.{u} n ⟶ Institution.room.{u} where
  sen := toFullSentence
  mod := fullModelReduct n
  sat T j := (EJdg.validIn_iff_valid (Discrete.as T) j.down.val).symm

/-- The coherent inclusion from a finite stage into full-universe MLTT. -/
def toFull (n : ℕ) : Inst.CoHom (finiteBundled.{u} n) Institution.bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => toFullCorridor n

end Apex

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
