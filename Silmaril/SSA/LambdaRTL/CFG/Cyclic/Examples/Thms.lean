module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms
import Silmaril.Semantics.Elgot.Thms
import Mathlib.Data.Nat.Pairing
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms

/-! The edge from block 20 to block 10 is taken twice. Block 10 stops when the
countdown reaches zero and returns the number of visits to block 20. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Examples

open Silmaril.Elgot

private def model : Model Unit Part Nat where
  unit := 0
  pair := Nat.pair
  inl := id
  inr := Nat.succ
  unpair value := pure (Nat.unpair value)
  split
    | 0 => pure (.inl 0)
    | n + 1 => pure (.inr n)
  app _ n := pure (n + 1)
  abort _ := Part.none

private theorem model_pairs : model.PairLawful :=
  ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩

-- Register false holds the countdown and register true counts visits.
private def registers (count visits : Nat) : Bool → Nat
  | false => count
  | true => visits

@[simp] private theorem registers_false (count visits : Nat) :
    registers count visits false = count := rfl

@[simp] private theorem registers_true (count visits : Nat) :
    registers count visits true = visits := rfl

private def headerWith {F : Type} (discriminant : Op Bool F) : Block Bool Nat F :=
  ⟨false, .term (.case discriminant false (.br 99 (.var true)) false (.br 20 (.var false)))⟩

private def header : Block Bool Nat Unit := headerWith (.val (.var false))

private def loop : CFG Bool Nat Unit :=
  ⟨.term (.br 10 (.var false)),
    [(10, header), (20, ⟨false, .let1 true (.app () (.var true)) (.term (.br 10 (.var false)))⟩)]⟩

private theorem updateCount (count visits next : Nat) :
    upd (registers count visits) false next = registers next visits := by
  funext reg
  cases reg <;> rfl

private theorem updateVisits (count visits next : Nat) :
    upd (registers count visits) true next = registers count next := by
  funext reg
  cases reg <;> rfl

private theorem header_more (count visits : Nat) :
    step model loop.blocks (10, count + 1, registers (count + 1) visits) =
      Part.some (.inr (20, count, registers count visits)) := by
  simp [step, loop, header, headerWith, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, model]

private theorem body_step (count visits : Nat) :
    step model loop.blocks (20, count, registers count visits) =
      Part.some (.inr (10, count, registers count (visits + 1))) := by
  simp [step, loop, List.lookup, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, updateVisits, model]

private theorem header_exit (visits : Nat) :
    step model loop.blocks (10, 0, registers 0 visits) =
      Part.some (.inr (99, visits, registers 0 visits)) := by
  simp [step, loop, header, headerWith, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, model]

private theorem exit_step (visits : Nat) :
    step model loop.blocks (99, visits, registers 0 visits) =
      Part.some (.inl (99, visits, registers 0 visits)) := rfl

-- The second and fourth transitions take the back edge and pass the updated store.
private theorem loop_returns :
    Cyclic.run model loop (registers 2 0) = Part.some (99, 2, registers 0 2) := by
  change iter (step model loop.blocks) (10, 2, registers 2 0) = Part.some _
  apply Part.eq_some_iff.mpr
  apply (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
  exact .more (Part.eq_some_iff.mp (header_more 1 0)) <|
    .more (Part.eq_some_iff.mp (body_step 1 0)) <|
    .more (Part.eq_some_iff.mp (header_more 0 1)) <|
    .more (Part.eq_some_iff.mp (body_step 0 1)) <|
    .more (Part.eq_some_iff.mp (header_exit 2)) <|
    .done (Part.eq_some_iff.mp (exit_step 2))

private def versionedInput (reg : Bool × Nat) : Nat :=
  if reg.2 = 0 then registers 2 0 reg.1 else 0

private def expectedBackEdgeBlock : Block (Bool × Nat) Nat Unit :=
  ⟨(false, 0), .let2 (false, 1) (false, 2) (.val (.var (false, 0))) <|
    .let2 (true, 3) (true, 4) (.val (.var (false, 2))) <|
    .let1 (true, 5) (.app () (.var (true, 3))) <|
    .term (.br 10 (.pair (.var (false, 1)) (.pair (.var (true, 5)) .unit)))⟩

-- Block 20 packs the new version of the visits register on its back edge.
example : (Versioning.compile loop).blocks.lookup 20 = some expectedBackEdgeBlock := by decide

-- The generated entry sends countdown 2 and one slot for the visits register.
example : (Versioning.compile loop).entry.evalJump model versionedInput =
    Part.some (10, Nat.pair 2 (Nat.pair 0 0)) :=
  rfl

-- The compiled table reaches the same exit after the genuine back edges.
example : Cyclic.runSSA model (Versioning.compile loop) versionedInput = Part.some (99, 2) := by
  rw [← Versioning.run_commutes model model_pairs loop]
  change obs <$> Cyclic.run model loop (registers 2 0) = _
  rw [loop_returns]
  rfl

-- Suffix lookup reports the label of the first backward transfer as its exit.
example : loop.run model (registers 2 0) = Part.some (10, 1, registers 1 1) := by
  simp [CFG.run, loop, header, headerWith, jump, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, updateVisits, model]

example : ¬ IsForward loop := by
  intro forward
  have bad := forward.2.1 10 (by simp [Body.targets, Term.targets])
  simp [loop, List.lookup] at bad

private def forwardGraph : CFG Bool Nat Unit :=
  ⟨loop.entry, [(10, header), (20, ⟨false, .term (.br 99 (.var true))⟩)]⟩

example (store : Bool → Nat) :
    Cyclic.run model forwardGraph store = forwardGraph.run model store :=
  run_eq_forward model forwardGraph (by
    simp [IsForward, ForwardTargets, forwardGraph, header, headerWith, Body.targets, Term.targets, List.lookup])
    store

/-! ## The named-to-Isotope interface on the countdown -/

open Silmaril.Isotope (Value BoundCtx)
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

private def captures : Fin 2 → Bool := Fin.cases false (fun _ => true)

private def num : Ty Unit := .base ()

private def packet (count : Ty Unit) : Ty Unit := .product count (.product num .unit)

private def captureTypes (count : Ty Unit) : BoundCtx (Ty Unit) 2 := .snoc (.snoc .nil num) count

private instance : HasTy Unit (Ty Unit) where
  src _ := num
  trg _ := num

private def originalFlat := (NamedFlat.compile loop [99] captures).get (by decide)

-- The actual original table scopes successfully. Its numeric discriminant
-- fails exact checking at the numeric profile.
example : NamedFlat.check originalFlat (captureTypes num) (fun _ => packet num) (fun _ => num) =
    false := by decide

private theorem noSelfSum (A B : Ty Unit) : Ty.coprod A B ≠ B := by
  intro eq
  have size := congrArg sizeOf eq
  simp at size

private theorem variableType {n : Nat} {ctx : BoundCtx (Ty Unit) n} {i : Fin n} {A : Ty Unit}
    (typed : Silmaril.Isotope.LetCase.LocallyNameless.HasType Unit
      (.nil : Silmaril.Isotope.Ctx Empty (Ty Unit)) ctx (.bv i) A) :
    A = ctx.get i := by
  cases typed
  rfl

-- Any stable countdown type shared by both label profiles would have to be
-- its own right summand. The obstruction is on the actual elaborated block.
example (count visits : Ty Unit) (inputTypes : BoundCtx (Ty Unit) 2)
    (exitTypes : Fin 1 → Ty Unit) :
    ¬ originalFlat.HasType inputTypes (fun _ => .product count (.product visits .unit)) exitTypes := by
  intro typed
  have headerType := typed.block ⟨0, by decide⟩
  change Silmaril.Isotope.LambdaSSA.Flat.HasType _ _
    (.let₂ (.bv 0) (.let₂ (.bv 0) (.case (.bv 3) (.br 2 (.bv 2))
      (.br 1 (.pair (.bv 0) (.pair (.bv 2) .unit)))))) at headerType
  cases headerType with
  | let₂ arg rest =>
    have eq := variableType arg
    change Ty.product _ _ = Ty.product count (.product visits .unit) at eq
    obtain ⟨rfl, rfl⟩ := Ty.product.inj eq
    cases rest with
    | let₂ arg rest =>
      have eq := variableType arg
      change Ty.product _ _ = Ty.product visits .unit at eq
      obtain ⟨rfl, rfl⟩ := Ty.product.inj eq
      cases rest with
      | case discr _ right =>
        have shape := variableType discr
        cases right with
        | br arg =>
          cases arg with
          | pair countArg _ =>
            have same := variableType countArg
            exact noSelfSum _ _ (shape.trans same)

private inductive Primitive
  | classify
  | increment

private instance : HasTy Primitive (Ty Unit) where
  src _ := num
  trg
    | .classify => .coprod num num
    | .increment => num

-- Keep the same source table and back edge, exposing the numeric split as a
-- typed primitive that returns a tagged sum.
private def profiledLoop : CFG Bool Nat Primitive :=
  let renamed := loop.mapOp fun _ => Primitive.increment
  { renamed with blocks := renamed.blocks.map fun item =>
    if item.1 = 10 then (item.1, headerWith (.app .classify (.var false))) else item }

private def admitted :=
  (NamedFlat.compileTyped profiledLoop [99] captures (captureTypes num)
    (fun _ => packet num) (fun _ => num)).get (by decide)

example : admitted.val.HasType (captureTypes num) (fun _ => packet num) (fun _ => num) :=
  admitted.property.2

private def prim : Primitive → Value Nat → Part (Value Nat)
  | .classify, .atom 0 => Part.some (.inl (.atom 0))
  | .classify, .atom (n + 1) => Part.some (.inr (.atom n))
  | .increment, .atom n => Part.some (.atom (n + 1))
  | _, _ => Part.none

private def taggedStore (count visits : Nat) : Bool → Value Nat
  | false => .atom count
  | true => .atom visits

private def namedInput : Bool × Nat → Value Nat := fun name => taggedStore 2 0 name.1

private def capturedEnv : Env Nat := fun index => if index = 0 then .atom 2 else .atom 0

private def payload (count visits : Nat) : Value Nat :=
  .pair (.atom count) (.pair (.atom visits) .unit)

-- Entry goes to numeric slot zero (the first occurrence of label 10).
example : Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval (NamedFlat.instr prim) capturedEnv
    admitted.val.entry.erase () 0 (payload 2 0) () := by
  apply (NamedFlat.entry_iff prim (Versioning.compile profiledLoop) [99]
    (fun i => (captures i, 0)) admitted.property.1 namedInput capturedEnv ?_ 0 (payload 2 0)).mp
  · change (0, payload 2 0) ∈ (Part.some (10, payload 2 0) >>=
      NamedFlat.number (NamedFlat.labelIndex (Versioning.compile profiledLoop).blocks [99]))
    rw [Part.bind_eq_bind, Part.bind_some]
    exact Part.mem_some _
  · intro i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i

private def backEdgeIndex : Fin (Versioning.compile profiledLoop).blocks.length :=
  ⟨1, by decide⟩

private theorem backEdge_eval : Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval
    (NamedFlat.instr prim) (extend capturedEnv (payload 1 0))
    (admitted.val.block backEdgeIndex).erase () 0 (payload 1 1) () := by
  change Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval (NamedFlat.instr prim)
    (extend capturedEnv (payload 1 0))
    (.let₂ (.var 0) (.let₂ (.var 0) (.let₁ (.op .increment (.var 1))
      (.br 0 (.pair (.var 4) (.pair (.var 0) .unit)))))) () 0 (payload 1 1) ()
  exact .let₂ .var (.let₂ .var (.let₁ (.op .var (Part.mem_some _)) (.br (.pair .var (.pair .var .unit)))))

-- The same finite transfer is a hit in the compiled named lexical table.
example :
    (0, payload 1 1) ∈
      (Cyclic.stepSSA (NamedFlat.model prim) (Versioning.compile profiledLoop).blocks namedInput
        (20, payload 1 0) >>= Sum.elim (fun _ => Part.none)
          (NamedFlat.number (NamedFlat.labelIndex (Versioning.compile profiledLoop).blocks [99]))) :=
  (NamedFlat.step_iff prim (Versioning.compile profiledLoop) [99] (fun i => (captures i, 0))
    admitted.property.1 20 backEdgeIndex rfl namedInput capturedEnv (payload 1 0) 0 (payload 1 1)).mpr backEdge_eval

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Examples
