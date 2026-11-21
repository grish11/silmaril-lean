module

public section

namespace Silmaril.Wasm.Profiles

inductive Wasm1
inductive Wasm2
inductive Wasm3
inductive Lime
inductive FX

inductive GCMode where
  | mutable | immutable

inductive ExceptionMode where
  | internal | disabled

/-- Closed functional Core: the two parameters independently govern GC writes
and internal exceptions. Neither parameter chooses an execution policy. -/
inductive FunctionalCore (gc : GCMode) (exceptions : ExceptionMode)

abbrev Functional := FunctionalCore .mutable .internal
abbrev FunctionalNoExceptions := FunctionalCore .mutable .disabled
abbrev StrictWithExceptions := FunctionalCore .immutable .internal
abbrev Strict := FunctionalCore .immutable .disabled

end Silmaril.Wasm.Profiles
