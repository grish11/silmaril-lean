module

public import Silmaril.Logic.ManyValuedCatalogue.Defs
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.SplitIfs

/-! Discrete examples and application encodings from the many-valued logic catalogue. -/

@[expose] public section

namespace Silmaril.Logic.ManyValuedCatalogue

namespace Post

variable {n : ℕ}

/-- The cyclic predecessor of Post's (m)-valued algebra, where (m=n+2). -/
def neg (x : Grid n) : Grid n := x - 1

def and (x y : Grid n) : Grid n := min x y

def or (x y : Grid n) : Grid n := max x y

/-- The top `count` values form the designated segment. The article gives the
operation tables and leaves this parameter unspecified. -/
def designated (count : ℕ) (x : Grid n) : Prop := n + 2 - count ≤ x.val

end Post

/-- An ordinary Boolean degree or Bochvar's infectious intermediate value. -/
abbrev Bochvar := Option Bool

namespace Bochvar

/-- Lift a binary Boolean connective to the internal fragment. -/
def lift₂ (f : Bool → Bool → Bool) (x y : Bochvar) : Bochvar :=
  x.bind fun a => y.map (f a)

def neg (x : Bochvar) : Bochvar := x.map Bool.not

def and (x y : Bochvar) : Bochvar := lift₂ (· && ·) x y

def or (x y : Bochvar) : Bochvar := lift₂ (· || ·) x y

def imp (x y : Bochvar) : Bochvar := lift₂ (fun a b => !a || b) x y

def iff (x y : Bochvar) : Bochvar := lift₂ (· == ·) x y

def designated (x : Bochvar) : Prop := x = some true

/-- Identify the values by their indices in the order false, unknown, true. -/
def toGrid : Bochvar → Grid 1
  | some false => 0
  | none => 1
  | some true => 2

end Bochvar

namespace Rose

variable {A : Type*} [Lattice A] [BoundedOrder A] [DecidableEq A]

def and (x y : A) : A := x ⊓ y

def or (x y : A) : A := x ⊔ y

/-- The consequent is returned when the antecedent is the top value. -/
def imp (x y : A) : A := if x = ⊤ then y else ⊤

def neg (x : A) : A := imp x ⊥

def designated (x : A) : Prop := x = ⊤

/-- The unary operation indexed by an intermediate value exchanges it with top. -/
def swapTop (a : A) : Equiv.Perm A := Equiv.swap ⊤ a

/-- A bounded lattice of incomparable atoms. Three atoms give Rose's
five-element diamond in Figure 3. -/
inductive Diamond (n : ℕ) where
  | bot
  | atom (i : Fin n)
  | top
  deriving DecidableEq

namespace Diamond

variable {n : ℕ}

protected def le : Diamond n → Diamond n → Prop
  | .bot, _ | _, .top => True
  | .atom i, .atom j => i = j
  | _, _ => False

instance : PartialOrder (Diamond n) where
  le := Diamond.le
  le_refl x := by cases x <;> simp [Diamond.le]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp_all [Diamond.le]
  le_antisymm x y := by cases x <;> cases y <;> simp_all [Diamond.le]

instance : BoundedOrder (Diamond n) where
  top := .top
  bot := .bot
  le_top x := by cases x <;> trivial
  bot_le _ := trivial

protected def inf : Diamond n → Diamond n → Diamond n
  | .top, y => y
  | x, .top => x
  | .atom i, .atom j => if i = j then .atom i else .bot
  | _, _ => .bot

protected def sup : Diamond n → Diamond n → Diamond n
  | .bot, y => y
  | x, .bot => x
  | .atom i, .atom j => if i = j then .atom i else .top
  | _, _ => .top

instance : Lattice (Diamond n) where
  inf := Diamond.inf
  sup := Diamond.sup
  inf_le_left x y := by
    change Diamond.le (Diamond.inf x y) x
    cases x <;> cases y <;> simp [Diamond.inf, Diamond.le]
    split_ifs <;> simp_all
  inf_le_right x y := by
    change Diamond.le (Diamond.inf x y) y
    cases x <;> cases y <;> simp [Diamond.inf, Diamond.le]
    split_ifs <;> simp_all
  le_inf x y z := by
    change Diamond.le x y → Diamond.le x z → Diamond.le x (Diamond.inf y z)
    cases x <;> cases y <;> cases z <;> simp_all [Diamond.inf, Diamond.le]
  le_sup_left x y := by
    change Diamond.le x (Diamond.sup x y)
    cases x <;> cases y <;> simp [Diamond.sup, Diamond.le]
    split_ifs <;> simp_all
  le_sup_right x y := by
    change Diamond.le y (Diamond.sup x y)
    cases x <;> cases y <;> simp [Diamond.sup, Diamond.le]
    split_ifs <;> simp_all
  sup_le x y z := by
    change Diamond.le x z → Diamond.le y z → Diamond.le (Diamond.sup x y) z
    cases x <;> cases y <;> cases z <;> simp_all [Diamond.sup, Diamond.le]
    split_ifs <;> trivial

end Diamond

end Rose

/-- The ATPG alphabet records a known pair of outputs in the order
(fault-free, faulty), or an unknown joint observation. -/
abbrev FaultValue := Option (Bool × Bool)

namespace FaultValue

def zero : FaultValue := some (false, false)
def one : FaultValue := some (true, true)
def unknown : FaultValue := none
def d : FaultValue := some (true, false)
def dBar : FaultValue := some (false, true)

def faultFree (x : FaultValue) : Option Bool := x.map Prod.fst

def faulty (x : FaultValue) : Option Bool := x.map Prod.snd

end FaultValue

/-- Boolean indicator of the graph of a multi-output function. -/
def graphIndicator {Input Output : Type*} [DecidableEq Output]
    (f : Input → Output) (input : Input) (output : Output) : Bool :=
  decide (f input = output)

namespace Qudit

/-- A computational basis vector indexed by a discrete level.
For a qudit of dimension `d`, take complex amplitudes and `2 < d`. -/
def basis {d : ℕ} {R : Type*} [Zero R] [One R] (i : Fin d) : Fin d → R :=
  fun j => if j = i then 1 else 0

/-- Action of a permutation of basis labels on the amplitude vector. -/
def relabel {d : ℕ} {R : Type*} (p : Equiv.Perm (Fin d)) (state : Fin d → R) :
    Fin d → R :=
  state ∘ p.symm

end Qudit

end Silmaril.Logic.ManyValuedCatalogue
