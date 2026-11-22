module

public import Silmaril.ProofFormats.DaslSyntax.Defs
public import Silmaril.Formats.Dasl.Lift.Thms
public import Silmaril.Semantics.Naming.Lift.Thms
import Silmaril.Proofs.ProofFormats.DaslSyntax.Basic

public section

namespace Silmaril.ProofFormats.DaslSyntax

open Silmaril.Formats.Dasl
open Silmaril.Logic.Smt (SE)
open Silmaril.Semantics.Naming (Binding)

variable {Item Name : Type}

theorem read_render (slots : InlinePrefix) (policy : Placement) (form : SE) :
    read (render slots policy form) = some form :=
  Proofs.ProofFormats.DaslSyntax.read_render_at slots policy [] form

theorem edge_metadata (policy : Placement) (path : Path) {skip index : Nat} (inline_ : index < skip)
    (child : Value) : edge policy path skip index child = child := by
  simp [edge, Nat.not_le_of_gt inline_]

theorem edge_linkAll (path : Path) {skip index : Nat} (boundary : skip ≤ index) (child : Value) :
    edge linkAll path skip index child = Value.obj child := by simp [edge, linkAll, boundary]

theorem Syntax.recover_write (grammar : Syntax Item) (policy : Placement) (item : Item) :
    grammar.recover (grammar.write policy item) = some item := by
  simpa only [Syntax.recover, Syntax.write, read_render, Option.bind_some] using grammar.codec.recovers item

theorem Syntax.linkAll_optional {grammar : Syntax Item} {value : Value} {item : Item}
    (maximal : grammar.presents linkAll value item) : grammar.optional value item := ⟨linkAll, maximal⟩

theorem Syntax.optional_recover {grammar : Syntax Item} {value : Value} {item : Item}
    (matched : grammar.optional value item) : grammar.recover value = some item :=
  let ⟨policy, equal⟩ := matched; equal ▸ grammar.recover_write policy item

theorem Syntax.optional_binding (grammar : Syntax Item) : Binding grammar.optional :=
  fun _ _ _ first second =>
    Option.some.inj ((grammar.optional_recover first).symm.trans (grammar.optional_recover second))

theorem Syntax.named_binding (grammar : Syntax Item) {store : Store Name} (bound : store.Binding) :
    Binding (grammar.named store).represents := Formats.Dasl.Lift.name_binding bound grammar.optional_binding

theorem Syntax.recovery_coherent (grammar : Syntax Item) (left right : Placement) (item : Item) :
    grammar.recover (grammar.write left item) = grammar.recover (grammar.write right item) :=
  (grammar.recover_write left item).trans (grammar.recover_write right item).symm

theorem Syntax.normalize_of_optional {grammar : Syntax Item} {value : Value} {item : Item}
    (matched : grammar.optional value item) : grammar.normalize value = some (grammar.write linkAll item) := by
  rw [Syntax.normalize, grammar.optional_recover matched, Option.map_some]

theorem Syntax.mem_namesWhere {grammar : Syntax Item} {store : Store Name} {predicate : Item → Prop} {root : Name} :
    root ∈ grammar.namesWhere store predicate ↔ ∃ item, (grammar.named store).represents root item ∧ predicate item :=
  Semantics.Naming.Lift.mem_where_iff

theorem Syntax.mem_namesWhere_language {grammar : Syntax Item} {store : Store Name} {predicate : Item → Prop}
    {root : Name} : root ∈ grammar.namesWhere store predicate ↔
    ∃ value, ValueNames store root value ∧ value ∈ grammar.language predicate :=
  Proofs.ProofFormats.DaslSyntax.mem_names_language

theorem Syntax.namesWhere_mono (grammar : Syntax Item) (store : Store Name) {left right : Item → Prop}
    (implies : ∀ item, left item → right item) : grammar.namesWhere store left ⊆ grammar.namesWhere store right :=
  fun _ hit => let ⟨item, known, holds⟩ := Syntax.mem_namesWhere.mp hit
               Syntax.mem_namesWhere.mpr ⟨item, known, implies item holds⟩

theorem system_iff {context conclusion : Semantics.Naming.Lift.Coordinate}
    {source : Consequence.System context.Meaning conclusion.Meaning}
    {ctx : context.Surface} {result : conclusion.Surface} : system context conclusion source ctx result ↔
    ∃ premises statement, context.represents ctx premises ∧ conclusion.represents result statement ∧
      source premises statement :=
  ⟨fun ⟨⟨premises, statement, _⟩, ⟨left, right, _⟩, holds⟩ => ⟨premises, statement, left, right, holds⟩,
    fun ⟨premises, statement, left, right, holds⟩ => ⟨(premises, statement, ()), ⟨left, right, trivial⟩, holds⟩⟩

theorem system_of_match {context conclusion : Semantics.Naming.Lift.Coordinate}
    {source : Consequence.System context.Meaning conclusion.Meaning}
    {ctx : context.Surface} {result : conclusion.Surface} {premises : context.Meaning} {statement : conclusion.Meaning}
    (ctxBound : Binding context.represents) (resultBound : Binding conclusion.represents)
    (left : context.represents ctx premises) (right : conclusion.represents result statement) :
    system context conclusion source ctx result ↔ source premises statement :=
  system_iff.trans ⟨fun ⟨_, _, lc, rc, holds⟩ => ctxBound lc left ▸ resultBound rc right ▸ holds,
    fun holds => ⟨premises, statement, left, right, holds⟩⟩

theorem system_mono {context conclusion : Semantics.Naming.Lift.Coordinate}
    {left right : Consequence.System context.Meaning conclusion.Meaning} (implies : left ≤ right) :
    system context conclusion left ≤ system context conclusion right :=
  fun _ _ hit => let ⟨premises, statement, lc, rc, holds⟩ := system_iff.mp hit
                 system_iff.mpr ⟨premises, statement, lc, rc, implies premises statement holds⟩

end Silmaril.ProofFormats.DaslSyntax
