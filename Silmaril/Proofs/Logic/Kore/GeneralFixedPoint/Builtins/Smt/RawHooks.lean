module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Source

/-! Raw application steps use the interpreter's actual first declaration and the
source model's law on every argument tuple. No singleton argument assumption is
introduced when transporting the result through the builtin equivalences. -/
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Kore.GeneralFixedPoint (RawPattern)
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
variable {scope : Silmaril.Logic.Kore.Modules.Scope}

/-- Reindex an actual operation and its complete argument tuple together. -/
private theorem operation_transport
    (M : Silmaril.Logic.Matching.GeneralFixedPoint.Model scope.signature)
    {n : Nat} {w w' : Fin n → String} {s : String} (h : w = w')
    (op : scope.signature.operations n w s) (args : ∀ i, M.carrier (w i)) :
    M.operation op args = M.operation (h ▸ op) (h ▸ args) := by
  cases h
  rfl

private theorem operation_transport_val {n : Nat} {w w' : Fin n → String}
    {s : String} (h : w = w') (op : scope.signature.operations n w s) :
    (h ▸ op).val = op.val := by
  cases h
  rfl

private theorem argument_transport_heq
    (M : Silmaril.Logic.Matching.GeneralFixedPoint.Model scope.signature)
    {n : Nat} {w w' : Fin n → String} (h : w = w')
    (args : ∀ i, M.carrier (w i)) (i : Fin n) :
    HEq ((h ▸ args) i) (args i) := by
  cases h
  rfl

variable [sorts : SortBindings]

/-- Recover the exact declaration, binding and checked profile used by hook?.
The attached lookup is the same first-match lookup used by raw denotation. -/
theorem hook_selected (hooks : List HookBinding) (name : String) (h : Hook)
    (accepted : hook? scope hooks name = some h) :
    ∃ (d : {symbol // symbol ∈ scope.symbols}) (binding : HookBinding),
      scope.symbols.attach.find? (fun d => d.val.declaration.name == name) = some d ∧
      binding ∈ hooks ∧ binding.symbol = d.val ∧ binding.hook = h ∧
      h.valid d.val.declaration = true := by
  have lookup :
      (scope.symbols.attach.find? (fun d => d.val.declaration.name == name)).map Subtype.val =
        scope.symbols.find? (fun d => d.declaration.name == name) := by
    simpa using (List.find?_subtype (l := scope.symbols.attach)
      (f := fun d => d.val.declaration.name == name)
      (g := fun d => d.declaration.name == name) (fun _ _ => rfl))
  unfold hook? at accepted
  rw [← lookup] at accepted
  cases found : scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
  | none => simp [found] at accepted
  | some d =>
      simp only [found, Option.map_some, bind, Option.bind] at accepted
      cases bound : hooks.find? (fun b => b.symbol == d.val) with
      | none => simp [bound] at accepted
      | some binding =>
          simp only [bound] at accepted
          split at accepted
          · rename_i valid
            cases Option.some.inj accepted
            refine ⟨d, binding, rfl, List.mem_of_find?_eq_some bound, ?_, rfl, valid⟩
            simpa using List.find?_some bound
          · contradiction

/-- The complete raw INT.eq application, with arbitrary set-valued children. -/
theorem source_intEq {literalPrefix : String} {literals : List LiteralBinding}
    {hooks : List HookBinding} (M : Model scope literalPrefix literals hooks)
    (objects : Semantics.Values M.native) (fuel : Nat) (name : String)
    (d : {symbol // symbol ∈ scope.symbols}) (binding : HookBinding)
    (found : scope.symbols.attach.find? (fun d => d.val.declaration.name == name) = some d)
    (member : binding ∈ hooks) (declared : binding.symbol = d.val)
    (hook : binding.hook = .intEq)
    (inputs : d.val.declaration.arguments = [sorts.intSort, sorts.intSort])
    (output : d.val.declaration.result = sorts.boolSort)
    (raw other : RawPattern) (p q : Pattern .integer)
    (left : Semantics.denote scope [] M.native M.carriers fuel [] objects sorts.intSort raw =
      some {x | M.carriers.integer x ∈ p.denote (sourceValuation M.carriers objects)})
    (right : Semantics.denote scope [] M.native M.carriers fuel [] objects sorts.intSort other =
      some {x | M.carriers.integer x ∈ q.denote (sourceValuation M.carriers objects)}) :
    Semantics.denote scope [] M.native M.carriers (fuel + 1) [] objects sorts.boolSort
      (.app name [raw, other]) =
      some {x | M.carriers.boolean x ∈
        (Pattern.intEq p q).denote (sourceValuation M.carriers objects)} := by
  rcases d with ⟨⟨origin, ⟨declName, arguments, result⟩⟩, inScope⟩
  dsimp only at inputs output
  subst arguments
  subst result
  let w : Fin 2 → String := fun i => ([sorts.intSort, sorts.intSort] : List String)[i.val]
  let op : scope.signature.operations 2 w sorts.boolSort :=
    ⟨⟨origin, ⟨declName, [sorts.intSort, sorts.intSort], sorts.boolSort⟩⟩,
      inScope, by simp [w], rfl⟩
  have profile : w = (fun _ => sorts.intSort) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have graph (args : ∀ i, M.native.carrier (w i)) :
      M.native.operation op args = Set.singleton (M.carriers.boolean.symm
        (Silmaril.Logic.Kore.Operational.Conditional.intEqual (M.carriers.integer (args 0))
          (M.carriers.integer (args 1)))) := by
    rw [operation_transport M.native profile op args]
    have symbol : (profile ▸ op).val = binding.symbol := by
      rw [operation_transport_val]
      exact declared.symm
    rw [M.laws.intEq binding member hook (profile ▸ op) symbol]
    have first : (profile ▸ args) 0 = args 0 :=
      eq_of_heq (argument_transport_heq M.native profile args 0)
    have second : (profile ▸ args) 1 = args 1 :=
      eq_of_heq (argument_transport_heq M.native profile args 1)
    rw [first, second]
    rfl
  have one : (1 : Fin 2) = Fin.succ 0 := rfl
  simp only [Semantics.denote, found, List.length_cons, List.length_nil,
    Nat.reduceAdd, ↓reduceDIte, bind, Option.bind]
  simp only [Silmaril.Logic.Kore.Modules.Checking.collect, left, right, List.get_eq_getElem, List.getElem_cons_zero,
    List.getElem_cons_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    bind, Option.bind, Option.pure_def]
  apply congrArg some
  ext out
  simp only [Set.mem_ofPred_eq]
  with_unfolding_all change (∃ values : ∀ i, M.native.carrier (w i),
    (∀ i : Fin 2, values i ∈ Fin.cases
      (motive := fun i : Fin 2 => Set (M.native.carrier (w i)))
      {x | M.carriers.integer x ∈ p.denote (sourceValuation M.carriers objects)}
      (Fin.cases (motive := fun j : Fin 1 => Set (M.native.carrier (w j.succ)))
        {x | M.carriers.integer x ∈ q.denote (sourceValuation M.carriers objects)}
        (fun j : Fin 0 => Fin.elim0 j)) i) ∧
      out ∈ M.native.operation op values) ↔ _
  constructor
  · rintro ⟨values, inside, value⟩
    rw [graph values] at value
    have rightInside : M.carriers.integer (values 1) ∈
        q.denote (sourceValuation M.carriers objects) := by
      with_unfolding_all change (M.carriers.integer (values (Fin.succ 0)) ∈
        q.denote (sourceValuation M.carriers objects))
      simpa only [Fin.cases_zero, Fin.cases_succ, Set.mem_ofPred_eq] using inside (Fin.succ 0)
    refine ⟨M.carriers.integer (values 0), inside 0,
      M.carriers.integer (values 1), rightInside, ?_⟩
    change out = _ at value
    rw [value, Equiv.apply_symm_apply]
  · rintro ⟨x, hx, y, hy, value⟩
    refine ⟨Fin.cases (motive := fun i : Fin 2 => M.native.carrier (w i))
      (M.carriers.integer.symm x)
      (Fin.cases (motive := fun j : Fin 1 => M.native.carrier (w j.succ))
        (M.carriers.integer.symm y) (fun k : Fin 0 => Fin.elim0 k)), ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
        simpa only [one, Fin.cases_zero, Fin.cases_succ, Set.mem_ofPred_eq,
          Equiv.apply_symm_apply] using hy
    · rw [graph]
      change out = _
      apply M.carriers.boolean.injective
      with_unfolding_all change (M.carriers.boolean out =
        M.carriers.boolean (M.carriers.boolean.symm
          (Silmaril.Logic.Kore.Operational.Conditional.intEqual
            (M.carriers.integer (M.carriers.integer.symm x))
            (M.carriers.integer (M.carriers.integer.symm y)))))
      simpa only [Equiv.apply_symm_apply] using value

/-- Raw BOOL.not applies to each possible child value; it is not complement. -/
theorem source_boolNot {literalPrefix : String} {literals : List LiteralBinding}
    {hooks : List HookBinding} (M : Model scope literalPrefix literals hooks)
    (objects : Semantics.Values M.native) (fuel : Nat) (name : String)
    (d : {symbol // symbol ∈ scope.symbols}) (binding : HookBinding)
    (found : scope.symbols.attach.find? (fun d => d.val.declaration.name == name) = some d)
    (member : binding ∈ hooks) (declared : binding.symbol = d.val)
    (hook : binding.hook = .boolNot)
    (inputs : d.val.declaration.arguments = [sorts.boolSort])
    (output : d.val.declaration.result = sorts.boolSort)
    (raw : RawPattern) (p : Pattern .boolean)
    (child : Semantics.denote scope [] M.native M.carriers fuel [] objects sorts.boolSort raw =
      some {x | M.carriers.boolean x ∈ p.denote (sourceValuation M.carriers objects)}) :
    Semantics.denote scope [] M.native M.carriers (fuel + 1) [] objects sorts.boolSort
      (.app name [raw]) =
      some {x | M.carriers.boolean x ∈
        (Pattern.boolNot p).denote (sourceValuation M.carriers objects)} := by
  rcases d with ⟨⟨origin, ⟨declName, arguments, result⟩⟩, inScope⟩
  dsimp only at inputs output
  subst arguments
  subst result
  let w : Fin 1 → String := fun i => ([sorts.boolSort] : List String)[i.val]
  let op : scope.signature.operations 1 w sorts.boolSort :=
    ⟨⟨origin, ⟨declName, [sorts.boolSort], sorts.boolSort⟩⟩, inScope, by simp [w], rfl⟩
  have profile : w = (fun _ => sorts.boolSort) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have graph (args : ∀ i, M.native.carrier (w i)) :
      M.native.operation op args = Set.singleton (M.carriers.boolean.symm (!(M.carriers.boolean (args 0)))) := by
    rw [operation_transport M.native profile op args]
    have symbol : (profile ▸ op).val = binding.symbol := by
      rw [operation_transport_val]
      exact declared.symm
    rw [M.laws.boolNot binding member hook (profile ▸ op) symbol]
    have first : (profile ▸ args) 0 = args 0 :=
      eq_of_heq (argument_transport_heq M.native profile args 0)
    rw [first]
    rfl
  simp only [Semantics.denote, found, List.length_cons, List.length_nil,
    Nat.reduceAdd, ↓reduceDIte, bind, Option.bind]
  simp only [Silmaril.Logic.Kore.Modules.Checking.collect, child, List.get_eq_getElem, List.getElem_cons_zero,
    Fin.val_zero, bind, Option.bind, Option.pure_def]
  apply congrArg some
  ext out
  simp only [Set.mem_ofPred_eq]
  with_unfolding_all change (∃ values : ∀ i, M.native.carrier (w i),
    (∀ i : Fin 1, values i ∈ Fin.cases
      (motive := fun i : Fin 1 => Set (M.native.carrier (w i)))
      {x | M.carriers.boolean x ∈ p.denote (sourceValuation M.carriers objects)}
      (fun j : Fin 0 => Fin.elim0 j) i) ∧
      out ∈ M.native.operation op values) ↔ _
  constructor
  · rintro ⟨values, inside, value⟩
    rw [graph values] at value
    refine ⟨M.carriers.boolean (values 0), inside 0, ?_⟩
    change out = _ at value
    rw [value, Equiv.apply_symm_apply]
  · rintro ⟨x, hx, value⟩
    refine ⟨Fin.cases (motive := fun i : Fin 1 => M.native.carrier (w i))
      (M.carriers.boolean.symm x) (fun j : Fin 0 => Fin.elim0 j), ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      simpa using hx
    · rw [graph]
      change out = _
      apply M.carriers.boolean.injective
      simpa using value

end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
