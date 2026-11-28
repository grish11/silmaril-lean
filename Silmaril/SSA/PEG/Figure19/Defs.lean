module

public import Silmaril.SSA.PEG.Semantics.Demand

/-! # Figure 19 PEG admission with explicit eval depth conventions

The judgment uses the actual typed row table. Assumptions name θ rows
and their depths. The result type of each judgment is the row's sort.
The executable search builds a derivation with bounded recursion.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Figure19

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

inductive EvalDirection where
  | printed
  | inward
  deriving DecidableEq

/-- The printed premise and the parent-to-immediate-child premise used
by the structured frontend are distinct conventions. -/
def EvalDirection.Allows (direction : EvalDirection) (surrounding sampled : Nat) : Prop :=
  match direction with
  | .printed => surrounding = sampled + 1
  | .inward => sampled = surrounding + 1

instance (direction : EvalDirection) (surrounding sampled : Nat) :
    Decidable (direction.Allows surrounding sampled) := by
  cases direction <;> unfold EvalDirection.Allows <;> infer_instance

def EvalDirection.surrounding (direction : EvalDirection) (sampled : Nat) : Nat :=
  match direction with
  | .printed => sampled + 1
  | .inward => sampled - 1

abbrev Assumptions (n : Nat) := List (Nat × Fin n)

def nodeAt (g : Graph P params results n l) {t : Ty Data} (r : Ref g.sort t) :
    Node P params (Fin l) g.sort t :=
  r.typed ▸ g.node r.id

/-- All row rules of Figure 19. The fused eval/pass rule requires the
same loop key as well as the same depth, since the typed PEG preserves
distinct loop identities at equal depths. -/
inductive Derives (g : Graph P params results n l) (depth : Fin l → Nat)
    (direction : EvalDirection) : Nat → Assumptions n → Fin n → Prop where
  | param {cap ctx i} {p : Port params (g.sort i)} {args : Tuple (Ref g.sort) []}
      (row : g.node i = .ofLabel (.param p) args) : Derives g depth direction cap ctx i
  | op {cap ctx i ins} {opcode : P ins (g.sort i)} {args : Tuple (Ref g.sort) ins}
      (row : g.node i = .ofLabel (.op opcode) args)
      (children : ∀ slot : Fin ins.length,
        Derives g depth direction cap ctx (args.get (portAt ins slot)).id) :
      Derives g depth direction cap ctx i
  | phi {cap ctx i} {args : Tuple (Ref g.sort) [.bool, g.sort i, g.sort i]}
      (row : g.node i = .ofLabel .phi args)
      (cond : Derives g depth direction cap ctx (args.get .head).id)
      (yes : Derives g depth direction cap ctx (args.get (.tail .head)).id)
      (no : Derives g depth direction cap ctx (args.get (.tail (.tail .head))).id) :
      Derives g depth direction cap ctx i
  | theta {ctx i key before} {args : Tuple (Ref g.sort) [g.sort i, g.sort i]}
      (row : g.node i = .ofLabel (.theta key) args) (prev : depth key = before + 1)
      (initial : Derives g depth direction before ctx (args.get .head).id)
      (feedback : Derives g depth direction (depth key) ((depth key, i) :: ctx)
        (args.get (.tail .head)).id) :
      Derives g depth direction (depth key) ctx i
  | evalPass {cap ctx i key} {args : Tuple (Ref g.sort) [g.sort i, .count]}
      {test : Tuple (Ref g.sort) [.bool]}
      (row : g.node i = .ofLabel (.eval key) args)
      (pass : nodeAt g (args.get (.tail .head)) = .ofLabel (.pass key) test)
      (step : direction.Allows cap (depth key))
      (older : ∀ a ∈ ctx, a.1 < depth key)
      (value : Derives g depth direction (depth key) ctx (args.get .head).id)
      (predicate : Derives g depth direction (depth key) ctx (test.get .head).id) :
      Derives g depth direction cap ctx i
  | reduce {cap smaller ctx fewer i} (depthLe : smaller ≤ cap)
      (subset : ∀ a ∈ fewer, a ∈ ctx)
      (body : Derives g depth direction smaller fewer i) :
      Derives g depth direction cap ctx i
  | assume {ctx i key} {args : Tuple (Ref g.sort) [g.sort i, g.sort i]}
      (row : g.node i = .ofLabel (.theta key) args) (active : (depth key, i) ∈ ctx) :
      Derives g depth direction (depth key) ctx i

/-- A local consequence of a derivation at an eval row. The host
depth may be smaller than the requested cap by Type-Reduce. -/
def EvalBoundary (g : Graph P params results n l) (depth : Fin l → Nat)
    (direction : EvalDirection) (cap : Nat) (i : Fin n) : Prop :=
  match g.node i with
  | ⟨_, .eval key, args⟩ =>
    ∃ host, host ≤ cap ∧ direction.Allows host (depth key) ∧
      ∃ test, nodeAt g (args.get (.tail .head)) = .ofLabel (.pass key) test
  | _ => True

/-- Type-PEG applies at depth zero with no assumptions. Type-PEG-Context
applies it to every ordered, typed result of the graph. -/
def CFGContext (g : Graph P params results n l) (depth : Fin l → Nat)
    (direction : EvalDirection) : Prop :=
  ∀ slot : Fin results.length,
    Derives g depth direction 0 [] (g.roots.get (portAt results slot)).id

structure Derivation (g : Graph P params results n l) (depth : Fin l → Nat)
    (direction : EvalDirection) (cap : Nat) (ctx : Assumptions n) (i : Fin n) : Type where
  proves : Derives g depth direction cap ctx i

/-- Try the row rule, lowering to the declared depth when necessary.
At eval, Type-Reduce permits retaining only assumptions at shallower
depths than the sampled loop. Fuel bounds the search depth. -/
def checkAt (g : Graph P params results n l) (depth : Fin l → Nat) (direction : EvalDirection) :
    Nat → (cap : Nat) → (ctx : Assumptions n) → (i : Fin n) →
    Option (Derivation g depth direction cap ctx i)
  | 0, _, _, _ => none
  | fuel + 1, cap, ctx, i =>
    match row : g.node i with
    | ⟨_, .param _, _⟩ => some ⟨.param row⟩
    | ⟨ins, .op _, args⟩ =>
      let children (slot : Fin ins.length) :=
        checkAt g depth direction fuel cap ctx (args.get (portAt ins slot)).id
      if valid : ∀ slot, (children slot).isSome then
        some ⟨.op row (fun slot => ((children slot).get (valid slot)).proves)⟩
      else none
    | ⟨_, .phi, args⟩ => do
      let c ← checkAt g depth direction fuel cap ctx (args.get .head).id
      let t ← checkAt g depth direction fuel cap ctx (args.get (.tail .head)).id
      let f ← checkAt g depth direction fuel cap ctx (args.get (.tail (.tail .head))).id
      return ⟨.phi row c.proves t.proves f.proves⟩
    | ⟨_, .theta key, args⟩ => do
      if within : depth key ≤ cap then
        if active : (depth key, i) ∈ ctx then
          return ⟨.reduce within (fun _ h => h) (.assume row active)⟩
        else if prev : depth key = depth key - 1 + 1 then
          let initial ← checkAt g depth direction fuel (depth key - 1) ctx (args.get .head).id
          let feedback ← checkAt g depth direction fuel (depth key) ((depth key, i) :: ctx)
            (args.get (.tail .head)).id
          return ⟨.reduce within (fun _ h => h) (.theta row prev initial.proves feedback.proves)⟩
        else none
      else none
    | ⟨_, .eval key, args⟩ => do
      let surrounding := direction.surrounding (depth key)
      match pass : nodeAt g (args.get (.tail .head)) with
      | ⟨_, .pass passKey, test⟩ =>
        if valid : passKey = key ∧ surrounding ≤ cap ∧ direction.Allows surrounding (depth key) then
          let fewer := ctx.filter (fun a => decide (a.1 < depth key))
          let sampled ← checkAt g depth direction fuel (depth key) fewer (args.get .head).id
          let predicate ← checkAt g depth direction fuel (depth key) fewer (test.get .head).id
          have older : ∀ a ∈ fewer, a.1 < depth key := fun _ h =>
            of_decide_eq_true (List.mem_filter.mp h).2
          return ⟨.reduce valid.2.1 (fun _ h => (List.mem_filter.mp h).1)
            (.evalPass row (by simpa only [valid.1, Node.ofLabel] using pass)
              valid.2.2 older sampled.proves predicate.proves)⟩
        else none
      | _ => none
    | _ => none
termination_by structural fuel _ _ _ => fuel

/-- An additional representation check for the numbered loop forest.
Root loops have depth one, and immediate children increment the depth. -/
def FitsForest (forest : LoopForest l) (depth : Fin l → Nat) : Prop :=
  ∀ key, depth key = ((forest.parent key).map depth).getD 0 + 1

def inferDepth (forest : LoopForest l) : Nat → Fin l → Nat
  | 0, _ => 0
  | fuel + 1, key => ((forest.parent key).map (inferDepth forest fuel)).getD 0 + 1

structure Admission (g : Graph P params results n l) (direction : EvalDirection) where
  depth : Fin l → Nat
  forest : FitsForest g.forest depth
  typed : CFGContext g depth direction

/-- Check all designated roots. Unvisited rows are outside the typing
judgment. The depth map is checked independently of its inference. -/
def check (g : Graph P params results n l) (direction : EvalDirection) (fuel : Nat) :
    Option (Admission g direction) :=
  let depth := inferDepth g.forest l
  if forest : ∀ key, depth key = ((g.forest.parent key).map depth).getD 0 + 1 then
    let roots (slot : Fin results.length) :=
      checkAt g depth direction fuel 0 [] (g.roots.get (portAt results slot)).id
    if typed : ∀ slot, (roots slot).isSome then
      some ⟨depth, forest, fun slot => ((roots slot).get (typed slot)).proves⟩
    else none
  else none

/-- Bundle the Figure 19 derivation with an independent whole-table
rank certificate for repaired Figure 11 demands. -/
structure Guarded (g : Graph P params results n l) (direction : EvalDirection) where
  admission : Admission g direction
  rank : DemandRank n l
  ranked : rank.check g = true

def checkGuarded (g : Graph P params results n l) (direction : EvalDirection) (fuel : Nat)
    (rank : DemandRank n l) : Option (Guarded g direction) := do
  let admission ← check g direction fuel
  if ok : rank.check g = true then some ⟨admission, rank, ok⟩ else none

end Silmaril.SSA.PEG.Figure19
