module

public import Silmaril.Wasi.Component.Accept.Catalog.Defs

/-! # The acceptor interpretation catalog: checks

* every shape is covered by an interpretation or by the unsupported list, and not both;
* every concrete-module subject is one of `concreteModules` (so `tools/wasm-pages` publishes it);
* identifiers are unique;
* every interpretation over a specification component or a hypothesis is not marked as resting on
  execution.
-/

namespace Silmaril.Wasi.Accept.Catalog

example : ∀ s ∈ Shape.all,
    (entries.any (·.shape == s) || unsupported.any (·.shape == s)) = true := by decide

example : ∀ s ∈ Shape.all,
    (entries.any (·.shape == s) && unsupported.any (·.shape == s)) = false := by decide

example : (entries.map (·.id)).Nodup := by decide

example : ∀ e ∈ entries, ∀ s, e.subject.slug? = some s → s ∈ concreteModules.map (·.1) := by
  decide

example : ∀ e ∈ entries, (match e.subject, e.basis with
    | .specComponent _, .execution => false
    | _, _ => true) = true := by decide

end Silmaril.Wasi.Accept.Catalog
