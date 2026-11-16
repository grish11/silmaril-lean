module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Calculus.Defs
public import Silmaril.Logic.Reachability.Derivation.FirstOrder.RuleBlocks.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder.Step
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables Silmaril.Logic.FirstOrder.FiniteConnectives
variable {Sg : FOL.Signature}

/-- Each operational rule has its own arbitrary finite sorted telescope. -/
structure FormulaRule (cfg : Sg.S) where
  telescope : List Sg.S
  lhs : RulePattern cfg telescope
  rhs : RulePattern cfg telescope

def FormulaRule.scheme (M : FOL.Structure Sg) {cfg : Sg.S} (rule : FormulaRule cfg) :
    RuleSystem.Scheme (M.carrier cfg) where
  Parameters := BlockAssignment M rule.telescope
  lhs b w := Pattern.localHolds rule.lhs M
    (joinAssignment M (Γ := emptyContext) (fun i => i.elim0) rule.telescope b) w
  rhs b w := Pattern.localHolds rule.rhs M
    (joinAssignment M (Γ := emptyContext) (fun i => i.elim0) rule.telescope b) w

def schemes (M : FOL.Structure Sg) {cfg : Sg.S} {r : Nat}
    (rules : Fin r → FormulaRule cfg) : Fin r → RuleSystem.Scheme (M.carrier cfg) :=
  fun i => (rules i).scheme M

def implies {k : Nat} {Γ : Fin k → Sg.S}
    (p q : FOL.Formula Sg Γ) : FOL.Formula Sg Γ := .not (.and p (.not q))

/-- Read a captured snapshot at slot1, ignoring the current outcome at slot0.
Every other coordinate shifts once. This is not configuration-preserving weakening. -/
def snapshot {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (p : Pattern Sg cfg Γ) : Pattern Sg cfg (Fin.cases cfg Γ) :=
  rename Fin.succ (fun _ => rfl) p

def coverageFormula {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (P : Pattern Sg cfg Γ) : Pattern Sg cfg Γ :=
  implies P (finiteOr (List.ofFn fun i =>
    existsBlock cfg Γ (rules i).telescope
      (liftRule cfg Γ (rules i).telescope (rules i).lhs)))

/-- The source-state witness is shared by the claim and operational lhs. -/
def snapshotSource {cfg : Sg.S} {k : Nat} (Γ : Fin k → Sg.S)
    (xs : List Sg.S) (P : Pattern Sg cfg Γ) (lhs : RulePattern cfg xs) :
    Pattern Sg cfg (blockContext Γ xs) :=
  existsCaptured cfg cfg (blockContext Γ xs)
    (snapshot cfg (blockContext Γ xs)
      (.and (weakenBlock cfg Γ xs P) (liftRule cfg Γ xs lhs)))

/-- The same free rule block is used in the snapshotted lhs and current rhs.
Only the source configuration is existentially bound. -/
def successorsFormula {cfg : Sg.S} {k r : Nat} {Γ : Fin k → Sg.S}
    (rules : Fin r → FormulaRule cfg) (i : Fin r) (P Q : Pattern Sg cfg Γ) :
    Pattern Sg cfg (blockContext Γ (rules i).telescope) :=
  implies
    (.and (snapshotSource Γ (rules i).telescope P (rules i).lhs)
      (liftRule cfg Γ (rules i).telescope (rules i).rhs))
    (weakenBlock cfg Γ (rules i).telescope Q)

/-- Project the outer assignment from an arbitrary joined context. -/
def outerAssignment (M : FOL.Structure Sg) {k : Nat} (Γ : Fin k → Sg.S) :
    (xs : List Sg.S) → ((i : Fin (blockSize xs k)) → M.carrier (blockContext Γ xs i)) →
      ((i : Fin k) → M.carrier (Γ i))
  | [], d => d
  | _ :: xs, d => outerAssignment M Γ xs (fun i => d i.succ)

/-- Extract the independently sorted rule block, without choosing any defaults. -/
def blockAssignment (M : FOL.Structure Sg) {k : Nat} (Γ : Fin k → Sg.S) :
    (xs : List Sg.S) → ((i : Fin (blockSize xs k)) → M.carrier (blockContext Γ xs i)) →
      BlockAssignment M xs
  | [], _ => ()
  | _ :: xs, d => (d ⟨0, Nat.zero_lt_succ _⟩, blockAssignment M Γ xs (fun i => d i.succ))

end Silmaril.Logic.Reachability.Derivation.FirstOrder.Step
