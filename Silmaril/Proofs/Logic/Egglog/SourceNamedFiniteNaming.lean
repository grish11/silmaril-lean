module

public import Silmaril.Logic.Egglog.Source.Named.Representation.Naming.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.FiniteSupport
open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem Footprint.sortIndex_get {S : Core.Signature} (support : Footprint S)
    (sort : support.signature.S) : support.sorts.get (support.sortIndex sort) = sort.val :=
  Classical.choose_spec (List.mem_iff_get.mp sort.property)

theorem Footprint.nameIndex_name {S : Core.Signature} (support : Footprint S)
    (name : NamedSort support) : finiteName (support.nameIndex name).val = name.val :=
  Classical.choose_spec (List.mem_ofFn.mp name.property)

theorem Footprint.nameIndex_encodeSort {S : Core.Signature} (support : Footprint S)
    (sort : support.signature.S) :
    support.nameIndex (support.encodeSort sort) = support.sortIndex sort := by
  apply Fin.ext
  apply finiteName_injective
  exact support.nameIndex_name (support.encodeSort sort)

/-- Sorting retraction preserves actual ambient sorts, including aliases. -/
theorem Footprint.decode_encode_sort {S : Core.Signature} (support : Footprint S)
    (sort : support.signature.S) : support.decodeSort (support.encodeSort sort) = sort := by
  apply Subtype.ext
  change support.sorts.get (support.nameIndex (support.encodeSort sort)) = sort.val
  rw [support.nameIndex_encodeSort, support.sortIndex_get]

theorem Footprint.sortNames_nodup {S : Core.Signature} (support : Footprint S) :
    support.sortNames.Nodup := by
  apply List.nodup_ofFn.mpr
  intro left right same
  exact Fin.ext (finiteName_injective same)

theorem Footprint.sortNames_legal {S : Core.Signature} (support : Footprint S) :
    ∀ name ∈ support.sortNames, LegalName name := by
  intro name member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact finiteName_legal i.val

/-- The three disjoint name ranges concatenate into one injectively named
finite range, establishing global constructor/predicate/table kind separation. -/
theorem Footprint.symbolNames {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) :
    ((support.declarationData closed).constructors.map TotalDeclaration.name ++
      (support.declarationData closed).relations.map RelationDeclaration.name ++
      (support.declarationData closed).functions.map TotalDeclaration.name) =
      List.ofFn (fun i : Fin (support.constructors.length + support.relations.length +
        support.functions.length) => finiteName i.val) := by
  simp only [declarationData, List.map_ofFn]
  symm
  rw [List.ofFn_add, List.ofFn_add]
  rfl

/-- Actual checked declaration validity follows from finite full-profile closure.
Neither ambient symbol equality nor a globally named ambient signature is used. -/
theorem Footprint.declarationData_valid {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) : (support.declarationData closed).Valid := by
  refine ⟨support.sortNames_nodup, ?_, support.sortNames_legal, ?_, ?_⟩
  · rw [support.symbolNames closed]
    apply List.nodup_ofFn.mpr
    intro left right same
    exact Fin.ext (finiteName_injective same)
  · intro entry member
    rcases List.mem_append.mp member with constructor | function
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp constructor
      refine ⟨finiteName_legal _, ?_, ?_⟩
      · intro name inputMember
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp inputMember
        exact (support.encodeSort _).property
      · exact (support.encodeSort _).property
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp function
      refine ⟨finiteName_legal _, ?_, ?_⟩
      · intro name inputMember
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp inputMember
        exact (support.encodeSort _).property
      · exact (support.encodeSort _).property
  · intro entry member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    refine ⟨finiteName_legal _, ?_⟩
    intro name inputMember
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp inputMember
    exact (support.encodeSort _).property

noncomputable def Footprint.declarations {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) : Declarations :=
  ⟨support.declarationData closed, support.declarationData_valid closed⟩

/-- The local constructor at one actual ambient occurrence, with its exact
encoded full profile. This is the symbol used by the finite encoding map. -/
noncomputable def Footprint.constructorPacket {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.constructors.length) :
    Constructor (support.declarations closed).signature :=
  let symbol := support.constructors.get index
  let profile := closed.1 symbol (List.get_mem _ _)
  ⟨symbol.1, (fun i => support.encodeSort ⟨symbol.2.1 i, profile.2 i⟩),
    support.encodeSort ⟨symbol.2.2.1, profile.1⟩,
    ⟨support.constructorDeclaration closed index, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl, rfl⟩⟩

noncomputable def Footprint.relationPacket {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.relations.length) :
    Relation (support.declarations closed).signature :=
  let symbol := support.relations.get index
  let profile := closed.2.1 symbol (List.get_mem _ _)
  ⟨symbol.1, (fun i => support.encodeSort ⟨symbol.2.1 i, profile i⟩),
    ⟨support.relationDeclaration closed index, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl⟩⟩

noncomputable def Footprint.functionPacket {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.functions.length) :
    FunctionSymbol (support.declarations closed).signature :=
  let symbol := support.functions.get index
  let profile := closed.2.2 symbol (List.get_mem _ _)
  ⟨symbol.1, (fun i => support.encodeSort ⟨symbol.2.1 i, profile.2 i⟩),
    support.encodeSort ⟨symbol.2.2.1, profile.1⟩,
    ⟨support.functionDeclaration closed index, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl, rfl⟩⟩

/-- Globally unique local names determine arity, full profiles and symbols,
including when the two packed symbols initially have different dependent types. -/
theorem constructorPacket_name_unique {D : Declarations}
    (left right : Constructor D.signature)
    (same : left.2.2.2.val.name = right.2.2.2.val.name) : left = right := by
  rcases left with ⟨n, w, s, first⟩
  rcases right with ⟨m, v, t, second⟩
  have declaration := constructor_name_injective D first.property.1 second.property.1 same
  have arities : n = m := by
    have lengths := congrArg (fun d : TotalDeclaration => d.inputs.length) declaration
    simpa only [first.property.2.1, second.property.2.1, List.length_ofFn] using lengths
  subst m
  obtain ⟨inputs, output, symbol⟩ := constructor_profile_unique first second same
  subst v
  subst t
  have equal : first = second := eq_of_heq symbol
  subst second
  rfl

theorem relationPacket_name_unique {D : Declarations}
    (left right : Relation D.signature)
    (same : left.2.2.val.name = right.2.2.val.name) : left = right := by
  rcases left with ⟨n, w, first⟩
  rcases right with ⟨m, v, second⟩
  have unique : (D.data.relations.map RelationDeclaration.name).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp D.valid.2.1).1).2.1
  have declaration := List.inj_on_of_nodup_map unique first.property.1 second.property.1 same
  have arities : n = m := by
    have lengths := congrArg (fun d : RelationDeclaration => d.inputs.length) declaration
    simpa only [first.property.2, second.property.2, List.length_ofFn] using lengths
  subst m
  obtain ⟨inputs, symbol⟩ := relation_profile_unique first second same
  subst v
  have equal : first = second := eq_of_heq symbol
  subst second
  rfl

theorem functionPacket_name_unique {D : Declarations}
    (left right : FunctionSymbol D.signature)
    (same : left.2.2.2.val.name = right.2.2.2.val.name) : left = right := by
  rcases left with ⟨n, w, s, first⟩
  rcases right with ⟨m, v, t, second⟩
  have unique : (D.data.functions.map TotalDeclaration.name).Nodup :=
    (List.nodup_append.mp D.valid.2.1).2.1
  have declaration := List.inj_on_of_nodup_map unique first.property.1 second.property.1 same
  have arities : n = m := by
    have lengths := congrArg (fun d : TotalDeclaration => d.inputs.length) declaration
    simpa only [first.property.2.1, second.property.2.1, List.length_ofFn] using lengths
  subst m
  obtain ⟨inputs, output, symbol⟩ := function_profile_unique first second same
  subst v
  subst t
  have equal : first = second := eq_of_heq symbol
  subst second
  rfl

noncomputable def Footprint.constructorIndex {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor (support.declarations closed).signature) :
    Fin support.constructors.length :=
  Classical.choose (List.mem_ofFn.mp packet.2.2.2.property.1)

theorem Footprint.constructorIndex_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor (support.declarations closed).signature) :
    support.constructorDeclaration closed (support.constructorIndex closed packet) =
      packet.2.2.2.val :=
  Classical.choose_spec (List.mem_ofFn.mp packet.2.2.2.property.1)

theorem Footprint.constructorIndex_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.constructors.length) :
    support.constructorIndex closed (support.constructorPacket closed index) = index := by
  apply Fin.ext
  apply finiteName_injective
  exact congrArg TotalDeclaration.name (support.constructorIndex_declaration closed _)

theorem Footprint.constructorPacket_index {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor (support.declarations closed).signature) :
    support.constructorPacket closed (support.constructorIndex closed packet) = packet := by
  apply constructorPacket_name_unique
  exact congrArg TotalDeclaration.name (support.constructorIndex_declaration closed packet)

noncomputable def Footprint.relationIndex {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation (support.declarations closed).signature) :
    Fin support.relations.length :=
  Classical.choose (List.mem_ofFn.mp packet.2.2.property.1)

theorem Footprint.relationIndex_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation (support.declarations closed).signature) :
    support.relationDeclaration closed (support.relationIndex closed packet) =
      packet.2.2.val :=
  Classical.choose_spec (List.mem_ofFn.mp packet.2.2.property.1)

theorem Footprint.relationIndex_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.relations.length) :
    support.relationIndex closed (support.relationPacket closed index) = index := by
  apply Fin.ext
  apply Nat.add_left_cancel (n := support.constructors.length)
  apply finiteName_injective
  exact congrArg RelationDeclaration.name (support.relationIndex_declaration closed _)

theorem Footprint.relationPacket_index {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation (support.declarations closed).signature) :
    support.relationPacket closed (support.relationIndex closed packet) = packet := by
  apply relationPacket_name_unique
  exact congrArg RelationDeclaration.name (support.relationIndex_declaration closed packet)

noncomputable def Footprint.functionIndex {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol (support.declarations closed).signature) :
    Fin support.functions.length :=
  Classical.choose (List.mem_ofFn.mp packet.2.2.2.property.1)

theorem Footprint.functionIndex_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol (support.declarations closed).signature) :
    support.functionDeclaration closed (support.functionIndex closed packet) =
      packet.2.2.2.val :=
  Classical.choose_spec (List.mem_ofFn.mp packet.2.2.2.property.1)

theorem Footprint.functionIndex_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.functions.length) :
    support.functionIndex closed (support.functionPacket closed index) = index := by
  apply Fin.ext
  apply Nat.add_left_cancel (n := support.constructors.length + support.relations.length)
  apply finiteName_injective
  exact congrArg TotalDeclaration.name (support.functionIndex_declaration closed _)

theorem Footprint.functionPacket_index {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol (support.declarations closed).signature) :
    support.functionPacket closed (support.functionIndex closed packet) = packet := by
  apply functionPacket_name_unique
  exact congrArg TotalDeclaration.name (support.functionIndex_declaration closed packet)

noncomputable def Footprint.encodeConstructorFromIndex {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor S) (member : packet ∈ support.constructors)
    (index : Fin support.constructors.length) (same : support.constructors.get index = packet) :
    (support.declarations closed).signature.Op packet.1
      (fun i => support.encodeSort ⟨packet.2.1 i, (closed.1 packet member).2 i⟩)
      (support.encodeSort ⟨packet.2.2.1, (closed.1 packet member).1⟩) := by
  subst packet
  exact (support.constructorPacket closed index).2.2.2

theorem Footprint.encodeConstructorFromIndex_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor S) (member : packet ∈ support.constructors)
    (index : Fin support.constructors.length) (same : support.constructors.get index = packet) :
    (support.encodeConstructorFromIndex closed packet member index same).val =
      support.constructorDeclaration closed index := by
  subst packet
  rfl

noncomputable def Footprint.encodeConstructorAt {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor S) (member : packet ∈ support.constructors) :
    (support.declarations closed).signature.Op packet.1
      (fun i => support.encodeSort ⟨packet.2.1 i, (closed.1 packet member).2 i⟩)
      (support.encodeSort ⟨packet.2.2.1, (closed.1 packet member).1⟩) :=
  support.encodeConstructorFromIndex closed packet member
    (Classical.choose (List.mem_iff_get.mp member))
    (Classical.choose_spec (List.mem_iff_get.mp member))

theorem Footprint.encodeConstructorAt_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor S) (member : packet ∈ support.constructors) :
    (support.encodeConstructorAt closed packet member).val =
      support.constructorDeclaration closed (Classical.choose (List.mem_iff_get.mp member)) :=
  support.encodeConstructorFromIndex_declaration closed packet member _ _

noncomputable def Footprint.encodeRelationFromIndex {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation S) (member : packet ∈ support.relations)
    (index : Fin support.relations.length) (same : support.relations.get index = packet) :
    (support.declarations closed).signature.Rel packet.1
      (fun i => support.encodeSort ⟨packet.2.1 i, (closed.2.1 packet member) i⟩) := by
  subst packet
  exact (support.relationPacket closed index).2.2

theorem Footprint.encodeRelationFromIndex_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation S) (member : packet ∈ support.relations)
    (index : Fin support.relations.length) (same : support.relations.get index = packet) :
    (support.encodeRelationFromIndex closed packet member index same).val =
      support.relationDeclaration closed index := by
  subst packet
  rfl

noncomputable def Footprint.encodeRelationAt {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation S) (member : packet ∈ support.relations) :
    (support.declarations closed).signature.Rel packet.1
      (fun i => support.encodeSort ⟨packet.2.1 i, (closed.2.1 packet member) i⟩) :=
  support.encodeRelationFromIndex closed packet member
    (Classical.choose (List.mem_iff_get.mp member))
    (Classical.choose_spec (List.mem_iff_get.mp member))

theorem Footprint.encodeRelationAt_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation S) (member : packet ∈ support.relations) :
    (support.encodeRelationAt closed packet member).val =
      support.relationDeclaration closed (Classical.choose (List.mem_iff_get.mp member)) :=
  support.encodeRelationFromIndex_declaration closed packet member _ _

noncomputable def Footprint.encodeFunctionFromIndex {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol S) (member : packet ∈ support.functions)
    (index : Fin support.functions.length) (same : support.functions.get index = packet) :
    (support.declarations closed).signature.Function packet.1
      (fun i => support.encodeSort ⟨packet.2.1 i, (closed.2.2 packet member).2 i⟩)
      (support.encodeSort ⟨packet.2.2.1, (closed.2.2 packet member).1⟩) := by
  subst packet
  exact (support.functionPacket closed index).2.2.2

theorem Footprint.encodeFunctionFromIndex_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol S) (member : packet ∈ support.functions)
    (index : Fin support.functions.length) (same : support.functions.get index = packet) :
    (support.encodeFunctionFromIndex closed packet member index same).val =
      support.functionDeclaration closed index := by
  subst packet
  rfl

noncomputable def Footprint.encodeFunctionAt {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol S) (member : packet ∈ support.functions) :
    (support.declarations closed).signature.Function packet.1
      (fun i => support.encodeSort ⟨packet.2.1 i, (closed.2.2 packet member).2 i⟩)
      (support.encodeSort ⟨packet.2.2.1, (closed.2.2 packet member).1⟩) :=
  support.encodeFunctionFromIndex closed packet member
    (Classical.choose (List.mem_iff_get.mp member))
    (Classical.choose_spec (List.mem_iff_get.mp member))

theorem Footprint.encodeFunctionAt_declaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol S) (member : packet ∈ support.functions) :
    (support.encodeFunctionAt closed packet member).val =
      support.functionDeclaration closed (Classical.choose (List.mem_iff_get.mp member)) :=
  support.encodeFunctionFromIndex_declaration closed packet member _ _

abbrev TotalProfile (S : Core.Signature) := Σ n, (Fin n → S.S) × S.S

def constructorProfile {S : Core.Signature} (packet : Constructor S) : TotalProfile S :=
  ⟨packet.1, packet.2.1, packet.2.2.1⟩
def relationProfile {S : Core.Signature} (packet : Relation S) : Σ n, Fin n → S.S :=
  ⟨packet.1, packet.2.1⟩
def functionProfile {S : Core.Signature} (packet : FunctionSymbol S) : TotalProfile S :=
  ⟨packet.1, packet.2.1, packet.2.2.1⟩

noncomputable def Footprint.supportConstructorPacket {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.constructors.length) :
    Constructor support.signature :=
  support.constructorFromMember closed ⟨support.constructors.get index, List.get_mem _ _⟩

noncomputable def Footprint.supportRelationPacket {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.relations.length) :
    Relation support.signature :=
  support.relationFromMember closed ⟨support.relations.get index, List.get_mem _ _⟩

noncomputable def Footprint.supportFunctionPacket {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.functions.length) :
    FunctionSymbol support.signature :=
  support.functionFromMember closed ⟨support.functions.get index, List.get_mem _ _⟩

theorem constructor_of_profile {S : Core.Signature} (packet : Constructor S)
    (profile : TotalProfile S) (same : profile = constructorProfile packet) :
    ∃ symbol : S.Op profile.1 profile.2.1 profile.2.2,
      (⟨profile.1, profile.2.1, profile.2.2, symbol⟩ : Constructor S) = packet := by
  subst profile
  refine ⟨packet.2.2.2, ?_⟩
  rcases packet with ⟨n, w, s, symbol⟩
  rfl

theorem relation_of_profile {S : Core.Signature} (packet : Relation S)
    (profile : Σ n, Fin n → S.S) (same : profile = relationProfile packet) :
    ∃ symbol : S.Rel profile.1 profile.2,
      (⟨profile.1, profile.2, symbol⟩ : Relation S) = packet := by
  subst profile
  refine ⟨packet.2.2, ?_⟩
  rcases packet with ⟨n, w, symbol⟩
  rfl

theorem function_of_profile {S : Core.Signature} (packet : FunctionSymbol S)
    (profile : TotalProfile S) (same : profile = functionProfile packet) :
    ∃ symbol : S.Function profile.1 profile.2.1 profile.2.2,
      (⟨profile.1, profile.2.1, profile.2.2, symbol⟩ : FunctionSymbol S) = packet := by
  subst profile
  refine ⟨packet.2.2.2, ?_⟩
  rcases packet with ⟨n, w, s, symbol⟩
  rfl

theorem Footprint.decode_constructor_profile {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor (support.declarations closed).signature) :
    (⟨packet.1, (fun i => support.decodeSort (packet.2.1 i)), support.decodeSort packet.2.2.1⟩ : TotalProfile support.signature) =
      constructorProfile (support.supportConstructorPacket closed (support.constructorIndex closed packet)) := by
  conv_lhs => rw [← support.constructorPacket_index closed packet]
  simp only [constructorPacket, supportConstructorPacket, constructorFromMember, constructorProfile,
    decode_encode_sort]

noncomputable def Footprint.decodeConstructor {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor (support.declarations closed).signature) :
    support.signature.Op packet.1 (fun i => support.decodeSort (packet.2.1 i))
      (support.decodeSort packet.2.2.1) :=
  Classical.choose (constructor_of_profile
    (support.supportConstructorPacket closed (support.constructorIndex closed packet))
    ⟨packet.1, (fun i => support.decodeSort (packet.2.1 i)), support.decodeSort packet.2.2.1⟩ (support.decode_constructor_profile closed packet))

theorem Footprint.decode_relation_profile {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation (support.declarations closed).signature) :
    (⟨packet.1, (fun i => support.decodeSort (packet.2.1 i))⟩ : Σ n, Fin n → support.signature.S) =
      relationProfile (support.supportRelationPacket closed (support.relationIndex closed packet)) := by
  conv_lhs => rw [← support.relationPacket_index closed packet]
  simp only [relationPacket, supportRelationPacket, relationFromMember, relationProfile,
    decode_encode_sort]

noncomputable def Footprint.decodeRelation {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation (support.declarations closed).signature) :
    support.signature.Rel packet.1 (fun i => support.decodeSort (packet.2.1 i)) :=
  Classical.choose (relation_of_profile
    (support.supportRelationPacket closed (support.relationIndex closed packet))
    ⟨packet.1, (fun i => support.decodeSort (packet.2.1 i))⟩ (support.decode_relation_profile closed packet))

theorem Footprint.decode_function_profile {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol (support.declarations closed).signature) :
    (⟨packet.1, (fun i => support.decodeSort (packet.2.1 i)), support.decodeSort packet.2.2.1⟩ : TotalProfile support.signature) =
      functionProfile (support.supportFunctionPacket closed (support.functionIndex closed packet)) := by
  conv_lhs => rw [← support.functionPacket_index closed packet]
  simp only [functionPacket, supportFunctionPacket, functionFromMember, functionProfile,
    decode_encode_sort]

noncomputable def Footprint.decodeFunction {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol (support.declarations closed).signature) :
    support.signature.Function packet.1 (fun i => support.decodeSort (packet.2.1 i))
      (support.decodeSort packet.2.2.1) :=
  Classical.choose (function_of_profile
    (support.supportFunctionPacket closed (support.functionIndex closed packet))
    ⟨packet.1, (fun i => support.decodeSort (packet.2.1 i)), support.decodeSort packet.2.2.1⟩ (support.decode_function_profile closed packet))

/-- The encoding/decoding maps are actual Core signature homomorphisms. -/
noncomputable def Footprint.encode {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) : support.signature ⟶ (support.declarations closed).signature where
  sorts := support.encodeSort
  ops := fun {n w s} symbol => support.encodeConstructorAt closed
    ⟨n, (fun i => (w i).val), s.val, symbol.val⟩ symbol.property
  rels := fun {n w} symbol => support.encodeRelationAt closed
    ⟨n, (fun i => (w i).val), symbol.val⟩ symbol.property
  functions := fun {n w s} symbol => support.encodeFunctionAt closed
    ⟨n, (fun i => (w i).val), s.val, symbol.val⟩ symbol.property

noncomputable def Footprint.decode {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) : (support.declarations closed).signature ⟶ support.signature where
  sorts := support.decodeSort
  ops := fun {n w s} symbol => support.decodeConstructor closed ⟨n, w, s, symbol⟩
  rels := fun {n w} symbol => support.decodeRelation closed ⟨n, w, symbol⟩
  functions := fun {n w s} symbol => support.decodeFunction closed ⟨n, w, s, symbol⟩

def mapConstructor {S T : Core.Signature} (morphism : S ⟶ T) : Constructor S → Constructor T
  | ⟨n, profile, output, symbol⟩ =>
      ⟨n, morphism.sorts ∘ profile, morphism.sorts output, morphism.ops symbol⟩

def mapRelation {S T : Core.Signature} (morphism : S ⟶ T) : Relation S → Relation T
  | ⟨n, profile, symbol⟩ => ⟨n, morphism.sorts ∘ profile, morphism.rels symbol⟩

def mapFunction {S T : Core.Signature} (morphism : S ⟶ T) : FunctionSymbol S → FunctionSymbol T
  | ⟨n, profile, output, symbol⟩ =>
      ⟨n, morphism.sorts ∘ profile, morphism.sorts output, morphism.functions symbol⟩

theorem Footprint.decode_constructor_spec {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor (support.declarations closed).signature) :
    mapConstructor (support.decode closed) packet =
      support.supportConstructorPacket closed (support.constructorIndex closed packet) := by
  rcases packet with ⟨n, w, s, symbol⟩
  exact Classical.choose_spec (constructor_of_profile _ _
    (support.decode_constructor_profile closed ⟨n, w, s, symbol⟩))

theorem Footprint.decode_relation_spec {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation (support.declarations closed).signature) :
    mapRelation (support.decode closed) packet =
      support.supportRelationPacket closed (support.relationIndex closed packet) := by
  rcases packet with ⟨n, w, symbol⟩
  exact Classical.choose_spec (relation_of_profile _ _
    (support.decode_relation_profile closed ⟨n, w, symbol⟩))

theorem Footprint.decode_function_spec {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol (support.declarations closed).signature) :
    mapFunction (support.decode closed) packet =
      support.supportFunctionPacket closed (support.functionIndex closed packet) := by
  rcases packet with ⟨n, w, s, symbol⟩
  exact Classical.choose_spec (function_of_profile _ _
    (support.decode_function_profile closed ⟨n, w, s, symbol⟩))

theorem Footprint.encode_constructor_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) {n : Nat} {w : Fin n → support.signature.S} {s : support.signature.S}
    (symbol : support.signature.Op n w s) :
    mapConstructor (support.encode closed) ⟨n, w, s, symbol⟩ =
      support.constructorPacket closed (Classical.choose (List.mem_iff_get.mp symbol.property)) := by
  apply constructorPacket_name_unique
  exact congrArg TotalDeclaration.name
    (support.encodeConstructorAt_declaration closed ⟨n, (fun i => (w i).val), s.val, symbol.val⟩ symbol.property)

theorem Footprint.decode_constructor_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.constructors.length) :
    mapConstructor (support.decode closed) (support.constructorPacket closed index) =
      support.supportConstructorPacket closed index := by
  rw [support.decode_constructor_spec, support.constructorIndex_packet]

theorem Footprint.constructor_retraction {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Constructor support.signature) :
    mapConstructor (support.encode closed ≫ support.decode closed) packet = packet := by
  rcases packet with ⟨n, w, s, symbol⟩
  change mapConstructor (support.decode closed)
    (mapConstructor (support.encode closed) ⟨n, w, s, symbol⟩) = ⟨n, w, s, symbol⟩
  rw [support.encode_constructor_packet, support.decode_constructor_packet]
  have same : support.constructors.get (Classical.choose (List.mem_iff_get.mp symbol.property)) =
      (⟨n, (fun i => (w i).val), s.val, symbol.val⟩ : Constructor S) := Classical.choose_spec (List.mem_iff_get.mp symbol.property)
  have entrySame :
      (⟨support.constructors.get (Classical.choose (List.mem_iff_get.mp symbol.property)),
        List.get_mem _ _⟩ : {packet : Constructor S // packet ∈ support.constructors}) =
      ⟨⟨n, (fun i => (w i).val), s.val, symbol.val⟩, symbol.property⟩ := Subtype.ext same
  unfold supportConstructorPacket
  rw [entrySame]
  rfl

theorem Footprint.encode_relation_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) {n : Nat} {w : Fin n → support.signature.S}
    (symbol : support.signature.Rel n w) :
    mapRelation (support.encode closed) ⟨n, w, symbol⟩ =
      support.relationPacket closed (Classical.choose (List.mem_iff_get.mp symbol.property)) := by
  apply relationPacket_name_unique
  exact congrArg RelationDeclaration.name
    (support.encodeRelationAt_declaration closed ⟨n, (fun i => (w i).val), symbol.val⟩ symbol.property)

theorem Footprint.decode_relation_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.relations.length) :
    mapRelation (support.decode closed) (support.relationPacket closed index) =
      support.supportRelationPacket closed index := by
  rw [support.decode_relation_spec, support.relationIndex_packet]

theorem Footprint.relation_retraction {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : Relation support.signature) :
    mapRelation (support.encode closed ≫ support.decode closed) packet = packet := by
  rcases packet with ⟨n, w, symbol⟩
  change mapRelation (support.decode closed)
    (mapRelation (support.encode closed) ⟨n, w, symbol⟩) = ⟨n, w, symbol⟩
  rw [support.encode_relation_packet, support.decode_relation_packet]
  have same : support.relations.get (Classical.choose (List.mem_iff_get.mp symbol.property)) =
      (⟨n, (fun i => (w i).val), symbol.val⟩ : Relation S) := Classical.choose_spec (List.mem_iff_get.mp symbol.property)
  have entrySame :
      (⟨support.relations.get (Classical.choose (List.mem_iff_get.mp symbol.property)),
        List.get_mem _ _⟩ : {packet : Relation S // packet ∈ support.relations}) =
      ⟨⟨n, (fun i => (w i).val), symbol.val⟩, symbol.property⟩ := Subtype.ext same
  unfold supportRelationPacket
  rw [entrySame]
  rfl

theorem Footprint.encode_function_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) {n : Nat} {w : Fin n → support.signature.S} {s : support.signature.S}
    (symbol : support.signature.Function n w s) :
    mapFunction (support.encode closed) ⟨n, w, s, symbol⟩ =
      support.functionPacket closed (Classical.choose (List.mem_iff_get.mp symbol.property)) := by
  apply functionPacket_name_unique
  exact congrArg TotalDeclaration.name
    (support.encodeFunctionAt_declaration closed ⟨n, (fun i => (w i).val), s.val, symbol.val⟩ symbol.property)

theorem Footprint.decode_function_packet {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.functions.length) :
    mapFunction (support.decode closed) (support.functionPacket closed index) =
      support.supportFunctionPacket closed index := by
  rw [support.decode_function_spec, support.functionIndex_packet]

theorem Footprint.function_retraction {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (packet : FunctionSymbol support.signature) :
    mapFunction (support.encode closed ≫ support.decode closed) packet = packet := by
  rcases packet with ⟨n, w, s, symbol⟩
  change mapFunction (support.decode closed)
    (mapFunction (support.encode closed) ⟨n, w, s, symbol⟩) = ⟨n, w, s, symbol⟩
  rw [support.encode_function_packet, support.decode_function_packet]
  have same : support.functions.get (Classical.choose (List.mem_iff_get.mp symbol.property)) =
      (⟨n, (fun i => (w i).val), s.val, symbol.val⟩ : FunctionSymbol S) := Classical.choose_spec (List.mem_iff_get.mp symbol.property)
  have entrySame :
      (⟨support.functions.get (Classical.choose (List.mem_iff_get.mp symbol.property)),
        List.get_mem _ _⟩ : {packet : FunctionSymbol S // packet ∈ support.functions}) =
      ⟨⟨n, (fun i => (w i).val), s.val, symbol.val⟩, symbol.property⟩ := Subtype.ext same
  unfold supportFunctionPacket
  rw [entrySame]
  rfl

theorem signature_hom_ext_packets {S T : Core.Signature} (first second : S ⟶ T)
    (sorts : first.sorts = second.sorts)
    (constructors : ∀ packet, mapConstructor first packet = mapConstructor second packet)
    (relations : ∀ packet, mapRelation first packet = mapRelation second packet)
    (functions : ∀ packet, mapFunction first packet = mapFunction second packet) : first = second := by
  rcases first with ⟨⟨⟨firstSorts, firstOps⟩, firstRels⟩, firstFunctions⟩
  rcases second with ⟨⟨⟨secondSorts, secondOps⟩, secondRels⟩, secondFunctions⟩
  change firstSorts = secondSorts at sorts
  cases sorts
  have operationEquality : @firstOps = @secondOps := by
    funext n w s symbol
    have packet := constructors ⟨n, w, s, symbol⟩
    have profile := eq_of_heq (Sigma.mk.inj packet).2
    have output := eq_of_heq (Sigma.mk.inj profile).2
    exact eq_of_heq (Sigma.mk.inj output).2
  have relationEquality : @firstRels = @secondRels := by
    funext n w symbol
    have packet := relations ⟨n, w, symbol⟩
    have profile := eq_of_heq (Sigma.mk.inj packet).2
    exact eq_of_heq (Sigma.mk.inj profile).2
  have functionEquality : @firstFunctions = @secondFunctions := by
    funext n w s symbol
    have packet := functions ⟨n, w, s, symbol⟩
    have profile := eq_of_heq (Sigma.mk.inj packet).2
    have output := eq_of_heq (Sigma.mk.inj profile).2
    exact eq_of_heq (Sigma.mk.inj output).2
  cases operationEquality
  cases relationEquality
  cases functionEquality
  rfl

/-- Concrete finite naming is a retraction on every sort and every actual
constructor/predicate/table symbol. Aliases do not weaken exactness. -/
theorem Footprint.encode_decode {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) : support.encode closed ≫ support.decode closed = 𝟙 support.signature := by
  apply signature_hom_ext_packets
  · funext sort
    exact support.decode_encode_sort sort
  · intro packet
    exact support.constructor_retraction closed packet
  · intro packet
    exact support.relation_retraction closed packet
  · intro packet
    exact support.function_retraction closed packet

end Silmaril.Logic.Egglog.Source.Named.FiniteSupport
