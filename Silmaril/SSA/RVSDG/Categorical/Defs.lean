module

public import Silmaril.SSA.RVSDG.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-! # Cartesian value denotations for acyclic RVSDG regions

The tensor is the chosen product in the value part of a Freyd model. Value
ports and explicit state *snapshots* denote objects of this category, so they
admit projection, duplication and discard. Primitives are value arrows.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (fst snd lift toUnit)
open scoped MonoidalCategory

universe u v d h w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]

namespace Categorical

/-- In a selector paired with a payload, inject a payload into the given arm. -/
def selectorLeg {K X : D} (tag : 𝟙_ D ⟶ K) : X ⟶ K ⊗ X :=
  lift (toUnit X ≫ tag) (𝟙 X)

/-- Finite distributivity in the specific form used by γ. The tags are ordered
by `Fin n`, and with any carried payload the tagged legs exhibit a coproduct
of `n` copies of that payload. -/
structure Selectors (D : Type d) [Category.{h} D] [CartesianMonoidalCategory D] where
  obj : Nat → D
  tag {n : Nat} : Fin n → (𝟙_ D ⟶ obj n)
  colimit (n : Nat) (X : D) :
    IsColimit (Cofan.mk (f := fun _ : Fin n => X) (obj n ⊗ X)
      (fun i => selectorLeg (tag i)))

variable (sel : Selectors D)

def portObj (value : V → D) (snapshot : S → D) : PortType V S → D
  | .value t => value t
  | .state t => snapshot t
  | .control n => sel.obj n

/-- Port zero is the left factor, with the unit at the right end. -/
def portsObj (F : PortType V S → D) : Ports (PortType V S) → D
  | [] => 𝟙_ D
  | t :: ts => F t ⊗ portsObj F ts

/-- All interpreted ports must be duplicable and discardable as values.
A state sort here is a data snapshot with these same permissions. -/
structure Model (Op : Dialect.{u, v} V S) (D : Type d)
    [Category.{h} D] [CartesianMonoidalCategory D] where
  selectors : Selectors D
  value : V → D
  snapshot : S → D
  primitive {ins outs : Ports (PortType V S)} : Op ins outs →
    (portsObj (portObj selectors value snapshot) ins ⟶
      portsObj (portObj selectors value snapshot) outs)

variable (m : Model Op D)

abbrev Model.port (t : PortType V S) : D := portObj m.selectors m.value m.snapshot t
abbrev Model.ports (ts : Ports (PortType V S)) : D := portsObj m.port ts

/-- Local tuples are grouped by producer, in ascending vertex-number order.
Only the interpretation of port objects determines the local scope. -/
@[simp] def localsObj (F : PortType V S → D) : List (Ports (PortType V S)) → D
  | [] => 𝟙_ D
  | ts :: past => portsObj F ts ⊗ localsObj F past

abbrev Model.locals (past : List (Ports (PortType V S))) : D := localsObj m.port past

abbrev Model.scope (args : Ports (PortType V S)) (past : List (Ports (PortType V S))) : D :=
  m.ports args ⊗ m.locals past

variable {args ins outs ts : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

def project : {ts : Ports (PortType V S)} → {t : PortType V S} →
    Port ts t → (m.ports ts ⟶ m.port t)
  | _, _, .head => fst _ _
  | _, _, .tail p => snd _ _ ≫ project p

def projectLocal : (past : List (Ports (PortType V S))) → (i : Fin past.length) →
    (m.locals past ⟶ m.ports past[i])
  | [], i => i.elim0
  | _ :: _, i => Fin.cases (motive := fun j => m.locals _ ⟶ m.ports _[j])
      (fst _ _) (fun j => snd _ _ ≫ projectLocal _ j) i

def readOrigin {t : PortType V S} : Origin args past t → (m.scope args past ⟶ m.port t)
  | .arg p => fst _ _ ≫ project m p
  | .output i p => snd _ _ ≫ projectLocal m past i ≫ project m p

/-- Assemble users in tuple order. Pairing permits fan-out and projection
permits unused origins. -/
def readWires : {ts : Ports (PortType V S)} → Wires args past ts → (m.scope args past ⟶ m.ports ts)
  | _, .nil => toUnit _
  | _, .cons origin rest => lift (readOrigin m origin) (readWires rest)

/-- Append one result tuple without changing any existing producer number. -/
def appendLocal (ts : Ports (PortType V S)) : (past : List (Ports (PortType V S))) →
    (m.locals past ⊗ m.ports ts ⟶ m.locals (past ++ [ts]))
  | [] => (λ_ _).hom ≫ (ρ_ _).inv
  | head :: tail => (α_ (m.ports head) (m.locals tail) (m.ports ts)).hom ≫
      (m.ports head ◁ appendLocal ts tail)

def appendScope (ts : Ports (PortType V S)) :
    m.scope args past ⊗ m.ports ts ⟶ m.scope args (past ++ [ts]) :=
  (α_ (m.ports args) (m.locals past) (m.ports ts)).hom ≫
    (m.ports args ◁ appendLocal m ts past)

/-- Retain the environment, then append the node's result on the right. -/
def extendScope (f : m.scope args past ⟶ m.ports ts) :
    m.scope args past ⟶ m.scope args (past ++ [ts]) :=
  lift (𝟙 _) f ≫ appendScope m ts

/-- Copair the arms under the finite distributor, with the selector first
and the payload in its original port order. -/
def dispatch {n : Nat} {X Y : D} (arms : Fin n → (X ⟶ Y)) : sel.obj n ⊗ X ⟶ Y :=
  (sel.colimit n X).desc (Cofan.mk Y arms)

def denoteShape (shape : Shape Op ins outs)
    (arms : Fin shape.regionCount → (m.ports shape.entry ⟶ m.ports shape.exit)) :
    m.ports ins ⟶ m.ports outs :=
  match shape with
  | .simple opcode => m.primitive opcode
  | .gamma _ => dispatch m.selectors arms

end Categorical

open Categorical (extendScope readWires denoteShape)

/-- Compositional interpretation of inductive bindings in an open region. -/
def Term.denoteOpen (m : Categorical.Model Op D) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → (m.scope args past ⟶ m.ports outs)
  | _, _, _, _, .ret results => readWires m results
  | _, _, _, _, .bind node children rest =>
    extendScope m (readWires m node.inputs ≫ denoteShape m node.shape
      (fun j => (ρ_ _).inv ≫ (children j).denoteOpen m)) ≫ rest.denoteOpen m

/-- Compose the numbered vertices in table order, preserving the ordered scope. -/
def Graph.denoteTable (m : Categorical.Model Op D) {args outs : Ports (PortType V S)} :
    (past sigs : List (Ports (PortType V S))) → (nodes : Nodes Op args past sigs) →
    ((i : Fin sigs.length) → Fin (nodes i).shape.regionCount →
      (m.ports (nodes i).shape.entry ⟶ m.ports (nodes i).shape.exit)) →
    Wires args (extend past sigs) outs → (m.scope args past ⟶ m.ports outs)
  | _, [], _, _, results => readWires m results
  | past, head :: tail, nodes, arms, results =>
    extendScope m (readWires m (nodes 0).inputs ≫ denoteShape m (nodes 0).shape (arms 0)) ≫
      denoteTable m (past ++ [head]) tail (fun i => nodes i.succ) (fun i => arms i.succ) results

/-- Interpret a numbered graph directly from its tables. -/
def Graph.denoteOpen (m : Categorical.Model Op D) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Graph Op args past sigs outs → (m.scope args past ⟶ m.ports outs)
  | _, _, past, sigs, .region nodes children results =>
    denoteTable m past sigs nodes (fun i j => (ρ_ _).inv ≫ (children i j).denoteOpen m) results

variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

def Term.denote (m : Categorical.Model Op D) (t : Term Op args [] sigs outs) :
    m.ports args ⟶ m.ports outs :=
  (ρ_ _).inv ≫ t.denoteOpen m

def Graph.denote (m : Categorical.Model Op D) (g : Graph Op args [] sigs outs) :
    m.ports args ⟶ m.ports outs :=
  (ρ_ _).inv ≫ g.denoteOpen m

namespace Categorical

/-- The runtime tuple representation encoded into the right-associated
Cartesian tensor used by the interpretation in types. -/
def pack {F : PortType V S → Type w} {ts : Ports (PortType V S)} :
    Tuple F ts → portsObj F ts
  | .nil => PUnit.unit
  | .cons x xs => (x, pack xs)

def unpack {F : PortType V S → Type w} :
    (ts : Ports (PortType V S)) → portsObj F ts → Tuple F ts
  | [], _ => .nil
  | _ :: ts, (x, xs) => .cons x (unpack ts xs)

/-- The finite tagged coproduct in types evaluates a copair by indexing with
the tag, passing the payload unchanged. -/
def typeSelectors : Selectors (Type w) where
  obj n := ULift (Fin n)
  tag i := ↾fun _ => ULift.up i
  colimit n X := Cofan.IsColimit.mk _
    (fun c => ↾fun (i, x) => c.inj i.down x)
    (fun _ _ => rfl)
    (fun _ f hf => by
      ext ⟨i, x⟩
      exact congrFun (congrArg (fun k => k.hom) (hf i.down)) x)

/-- Interpret primitives as their deterministic functions, conjugated by the
tuple representation. The rest of the semantics is the categorical fold. -/
def Model.ofRuntime (runtime : RVSDG.Model.{u, v, w} Op) : Model Op (Type w) where
  selectors := typeSelectors
  value := runtime.value
  snapshot := runtime.state
  primitive opcode := ↾fun input => pack (runtime.run opcode (unpack _ input))

end Categorical

end Silmaril.SSA.RVSDG
