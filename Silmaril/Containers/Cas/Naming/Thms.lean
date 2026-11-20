module

public import Silmaril.Containers.Cas.Naming.Defs
public import Silmaril.Semantics.Naming.Thms

public section

namespace Silmaril.Containers.Cas.Store

variable {D C : Type}

theorem relation_fillMissing (base defaults : Store D C) :
    (base.fillMissing defaults).relation = Semantics.Naming.fillMissing base.relation defaults.relation := by
  funext name payload
  cases hit : base name <;>
    simp [fillMissing, relation, Semantics.Naming.fillMissing, Semantics.Naming.graph, hit]

theorem le_fillMissing (base defaults : Store D C) : base.Le (base.fillMissing defaults) := by
  intro name payload hit
  exact (congrFun₂ (relation_fillMissing base defaults) name payload).mpr (.inl hit)

theorem relation_binding (store : Store D C) : Semantics.Naming.Binding store.relation :=
  Semantics.Naming.graph_binding store

theorem sound_iff_hashCompatible (hash : C → D) (store : Store D C) :
    Sound hash store ↔ Semantics.Naming.HashCompatible hash store.relation :=
  ⟨fun sound => by intro digest payload hit; exact sound digest payload hit,
   fun compatible digest payload hit => compatible (name := digest) (wire := payload) hit⟩

end Silmaril.Containers.Cas.Store
