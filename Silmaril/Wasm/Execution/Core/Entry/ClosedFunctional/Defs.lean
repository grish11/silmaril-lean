module

public import Silmaril.Wasm.Execution.Core.Entry.Determinism.Defs
public import Silmaril.Wasm.Profiles.Functional.Defs

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional

/-- A sufficient ready-store certificate, not an ISA or a module admission
test. It covers all allocated functions, including callees reached by
`call_ref`. No host binding is allowed. Use Core typing separately. -/
def Bodies {H : Type} (s : Store H) : Prop :=
  ∀ entry ∈ s.funcs, ∃ fn : Func, ∃ body : Profiles.FunctionalISA.Raw .immutable,
    entry.code = .wasm fn ∧ fn.body = body.erase

end Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional
