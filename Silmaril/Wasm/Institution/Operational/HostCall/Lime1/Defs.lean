module

public import Silmaril.Wasm.Lime1.Execution.Callout

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1

open Execution.Runtime (EvalCtx Frame FuncAddr MemAddr MemInst Result Value)
open Wasm.Lime1.Execution

/-- The designated memory is allocated in the base store. Its live byte array
may change, while its extent, declared limit and all other allocations stay fixed. -/
structure Memory32 {H : Type} (base : Store H) where
  address : MemAddr
  initial : MemInst
  allocated : base.memories[address.value]? = some initial

namespace Memory32

def store {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Store H :=
  setMemory base memory.address { memory.initial with data := bytes }

def Live {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Prop :=
  bytes.size = memory.initial.data.size

end Memory32

/-- One direct host target and its complete ordered numeric signature. -/
structure Site (H : Type) where
  address : FuncAddr
  type : Wasm.Lime1.FuncType
  code : H

def Site.Allocated {H : Type} (site : Site H) (base : Store H) : Prop :=
  base.funcs[site.address.value]? = some (.host site.type site.code)

def Site.Arguments {H : Type} (site : Site H) (args : List Value) : Prop :=
  args.map Value.type = site.type.params

def Site.TypedResult {H : Type} (site : Site H) : Result → Prop
  | .values vs => vs.map Value.type = site.type.results
  | .trap => True

/-- The embedding must reestablish the live store relation on every returned
outcome from this site with typed operands, including a returned trap. -/
def Site.Contract {H : Type} {base : Store H} (site : Site H) (memory : Memory32 base)
    (host : HostSemantics H) : Prop :=
  ∀ ⦃bytes args returned outcome⦄, memory.Live bytes → site.Arguments args →
    host site.code (memory.store bytes) args (.returned returned outcome) →
    ∃ next, memory.Live next ∧ returned = memory.store next ∧ site.TypedResult outcome

def Site.callout {H : Type} (site : Site H) (context : EvalCtx Wasm.Lime1.Instr) (args : List Value) :
    Execution.Runtime.Callout H Wasm.Lime1.Instr :=
  ⟨context, site.address, site.type, site.code, args⟩

def Site.pending {H : Type} (site : Site H) (s : Store H) (outer : Frame)
    (context : EvalCtx Wasm.Lime1.Instr) (args : List Value) : Config H :=
  ⟨s, outer, context.plug value (values args ++ [.invoke site.address])⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1
