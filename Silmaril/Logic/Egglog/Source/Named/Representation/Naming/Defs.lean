module

public import Silmaril.Logic.Egglog.Source.Named.Representation.Local.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Support.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.FiniteSupport

/-- Local sort spellings index the finite occurrence list. Repeated ambient sorts
may receive several aliases; no ambient equality instance or enumeration occurs. -/
def Footprint.sortNames {S : Core.Signature} (support : Footprint S) : List String :=
  List.ofFn (fun i : Fin support.sorts.length => finiteName i.val)

abbrev NamedSort {S : Core.Signature} (support : Footprint S) :=
  {name : String // name ∈ support.sortNames}

noncomputable def Footprint.sortIndex {S : Core.Signature} (support : Footprint S)
    (sort : support.signature.S) : Fin support.sorts.length :=
  Classical.choose (List.mem_iff_get.mp sort.property)

noncomputable def Footprint.nameIndex {S : Core.Signature} (support : Footprint S)
    (name : NamedSort support) : Fin support.sorts.length :=
  Classical.choose (List.mem_ofFn.mp name.property)

noncomputable def Footprint.encodeSort {S : Core.Signature} (support : Footprint S)
    (sort : support.signature.S) : NamedSort support :=
  ⟨finiteName (support.sortIndex sort).val, List.mem_ofFn.mpr ⟨support.sortIndex sort, rfl⟩⟩

noncomputable def Footprint.decodeSort {S : Core.Signature} (support : Footprint S)
    (name : NamedSort support) : support.signature.S :=
  ⟨support.sorts.get (support.nameIndex name), List.get_mem _ _⟩

/-- Each symbol occurrence receives its own finite local name. Repeated ambient
symbols become legitimate aliases rather than requiring dependent deduplication. -/
noncomputable def Footprint.constructorDeclaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.constructors.length) : TotalDeclaration :=
  let symbol := support.constructors.get index
  let profile := closed.1 symbol (List.get_mem _ _)
  ⟨finiteName index.val,
    List.ofFn (fun i => (support.encodeSort ⟨symbol.2.1 i, profile.2 i⟩).val),
    (support.encodeSort ⟨symbol.2.2.1, profile.1⟩).val⟩

noncomputable def Footprint.relationDeclaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.relations.length) : RelationDeclaration :=
  let symbol := support.relations.get index
  let profile := closed.2.1 symbol (List.get_mem _ _)
  ⟨finiteName (support.constructors.length + index.val),
    List.ofFn (fun i => (support.encodeSort ⟨symbol.2.1 i, profile i⟩).val)⟩

noncomputable def Footprint.functionDeclaration {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) (index : Fin support.functions.length) : TotalDeclaration :=
  let symbol := support.functions.get index
  let profile := closed.2.2 symbol (List.get_mem _ _)
  ⟨finiteName (support.constructors.length + support.relations.length + index.val),
    List.ofFn (fun i => (support.encodeSort ⟨symbol.2.1 i, profile.2 i⟩).val),
    (support.encodeSort ⟨symbol.2.2.1, profile.1⟩).val⟩

noncomputable def Footprint.declarationData {S : Core.Signature} (support : Footprint S)
    (closed : support.Closed) : DeclarationData :=
  ⟨support.sortNames, List.ofFn (support.constructorDeclaration closed),
    List.ofFn (support.relationDeclaration closed), List.ofFn (support.functionDeclaration closed)⟩

end Silmaril.Logic.Egglog.Source.Named.FiniteSupport
