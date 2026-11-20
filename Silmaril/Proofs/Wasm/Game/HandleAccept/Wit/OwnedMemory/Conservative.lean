module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Conservative.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Conservative

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
  Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Formats
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

theorem erase_checkValue {type : Stored.TypeOf} (observed : Observed)
    (complete : observed.Complete type) :
    (checkValue type observed).map Payload.erase =
      (Stored.checkValue type observed.value).mapError Issue.schema := by
  unfold checkValue Stored.checkValue
  split <;> simp_all [Observed.Complete, Payload.erase, Except.map, Except.mapError]

private theorem primitive_schema (primitive : WIT.Primitive) :
    checkSchema (.prim primitive) = .ok () ∧ Stored.checkSchema (.prim primitive) = .ok () := by
  have noBorrow : containsBorrow (.prim primitive : Stored.TypeOf) = false := rfl
  have noOwn : Stored.payloadContainsOwn (.prim primitive) = false := rfl
  have wellFormed : ValType.WellFormedCM (.prim primitive : Stored.TypeOf) := by
    refine ⟨.prim primitive, rfl, rfl, rfl, ?_⟩
    simp only [ValType.anySub, oversizedNode, layout]
    cases primitive <;> decide
  simp [checkSchema, Stored.checkSchema, noBorrow, noOwn, wellFormed]

private theorem primitive_check (primitive : WIT.Primitive) (value : Val) :
    (checkValue (.prim primitive) (Observed.ordinary value)).map Payload.erase =
      (Stored.checkValue (.prim primitive) value).mapError Issue.schema := by
  apply erase_checkValue
  cases value <;> rfl

set_option maxHeartbeats 300000 in
theorem primitive_lift {E : CoreEngine} {World : Type} (limits : Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (primitive : WIT.Primitive) (input : Stored.Input) :
    (fun result => result.map Payload.erase) <$>
        lift (World := World) limits quirks cx (.prim primitive) input =
      Except.mapError Issue.schema <$> Stored.lift limits quirks cx (.prim primitive) input := by
  unfold lift Stored.lift
  rw [(primitive_schema primitive).1, (primitive_schema primitive).2]
  simp only [map_bind]
  congr 1
  funext width
  cases input <;> dsimp only
  case memory ptr =>
    simp only [map_bind]
    congr 1
    funext _
    congr 1
    funext _
    simp only [loadAtWith, loadAt, carrier, bind_map_left, map_pure]
    congr 1
    funext value
    exact congrArg pure (primitive_check primitive value)
  case flat values =>
    by_cases types : values.map Stored.flatType = flatten width (.prim primitive : Stored.TypeOf)
    · have sameTypes : (values.map Stored.flatType != flatten width (.prim primitive : Stored.TypeOf)) = false := by
        simp [types]
      simp only [sameTypes, Bool.false_eq_true, ite_false, liftFlatAt, liftFlatAtWith,
        flatCarrier, bind_map_left, map_bind, map_pure]
      congr 1
      funext (value, _)
      exact congrArg pure (primitive_check primitive value)
    · simp [types]
      rfl

theorem erase_node (sig : Stored.Signature) (tag : sig.Tag) (payload : Payload (sig.payload tag))
    (children : List (Tree sig)) :
    Tree.erase (AST.node tag payload children) = AST.node tag payload.erase (children.map Tree.erase) := by
  let mapped := children.map Tree.erase
  let original : Σ count, Fin count → Stored.Tree sig :=
    ⟨children.length, fun index => (children.get index).erase⟩
  let erased : Σ count, Fin count → Stored.Tree sig := ⟨mapped.length, mapped.get⟩
  have length : original.1 = erased.1 := (List.length_map ..).symm
  have same : original = erased := Sigma.ext length ((Fin.heq_fun_iff length).2 (by
    intro index
    simp [original, erased, mapped]))
  exact congrArg (fun entry : Σ count, Fin count → Stored.Tree sig =>
    TExpr.tag ⟨tag, payload.erase⟩ entry.1 entry.2) same

theorem primitive_node {E : CoreEngine} {World : Type} (sig : Stored.Signature)
    (limits : Limits) (quirks : Quirks) (cx : LiftLowerContext E) (tag : sig.Tag)
    (primitive : WIT.Primitive) (type : sig.payload tag = .prim primitive) (input : Stored.Input)
    (children : List (Tree sig)) :
    (fun result => result.map Tree.erase) <$>
        buildNode (World := World) sig limits quirks cx tag input children =
      Except.mapError Issue.schema <$>
        Stored.buildNode sig limits quirks cx tag input (children.map Tree.erase) := by
  unfold buildNode Stored.buildNode
  rw [List.length_map]
  split
  · rfl
  · have sameLift : (fun result => result.map Payload.erase) <$>
          lift (World := World) limits quirks cx (sig.payload tag) input =
        Except.mapError Issue.schema <$> Stored.lift limits quirks cx (sig.payload tag) input :=
      type.symm ▸ primitive_lift limits quirks cx primitive input
    change (fun result => result.map Tree.erase) <$>
        ((fun result => result.map fun payload => AST.node tag payload children) <$>
          lift limits quirks cx (sig.payload tag) input) =
      Except.mapError Issue.schema <$>
        ((fun result => result.map fun payload => AST.node tag payload (children.map Tree.erase)) <$>
          Stored.lift limits quirks cx (sig.payload tag) input)
    calc
      _ = (fun result => result.map fun payload => AST.node tag payload (children.map Tree.erase)) <$>
          ((fun result => result.map Payload.erase) <$> lift limits quirks cx (sig.payload tag) input) := by
        simp only [Functor.map_map]
        congr 1
        funext result
        cases result <;> simp [Except.map, erase_node]
      _ = _ := by
        rw [sameLift]
        simp only [Functor.map_map]
        congr 1
        funext result
        cases result <;> rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Conservative
