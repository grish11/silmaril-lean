module

public import Silmaril.Machine.Abi.SystemV.Thms
public import Silmaril.X86.FnContract.Defs
public import Silmaril.Data.Layout.Header.Defs

/-!
# ABI conformance of a function: the statement

**`Conforms A M mode hdr f p code frame S`**: the machine code `code`, run on the machine `M`
and called as the ABI `A` requires for the prototype `p` that the C header `hdr` declares for
`f`, behaves as a conforming callee: every admitted call returns by `A`'s discipline, with a
result `A` reads back and that the C-level spec `S` allows, writing only memory that `S` or `A`
gives it. In total mode it also returns.

Every ingredient is a definition the statement names; nothing is an uninterpreted
"conforms" predicate and no signature is attached to a symbol by hand:

| ingredient | what fixes it |
| --- | --- |
| the ABI | `A : AbiDef`: a versioned identity and source (`id`, `source`), a data model, the C → ABI lowering (`lower`, which refuses what it does not support), and a `Convention` (`Machine.Abi.Convention`) giving `Entry` (argument placement, stack alignment, return address, direction flag, x87 mode, `%al` for varargs), `Return` (return address, `rsp + 8`, callee-saved registers, control state, thread pointer) and `ResultAt` (result read-back) |
| the prototype | `declared`: the header files `hdr` parse (`Data.Layout.Header.read`) to a header declaring `f` with a C prototype that `A.lower` maps to `p` |
| the code | `code : Code`: the bytes, where they are loaded, the entry offset and the function's extent; admitted states have them loaded and `rip` at the entry |
| admissible calls | `Admit`: a live machine state, `A.conv.Entry p a s` for the arguments `a`, the code placed, the return address outside the code, and `frame` bytes of usable stack below `rsp` (plus `A`'s incoming argument area) apart from the code; and `S.pre a s` (the C-level precondition: valid buffers, no undefined behaviour) |
| execution | `callModelOf M`: the **first return** of the machine `M` (`FnContract.FirstReturn`), so the result is read at the function's own return, not at a later state of the caller |
| return | `Good`: `A.conv.Return`, a result `r` with `A.conv.ResultAt` and `S.post`, and memory written only inside `S.writes` (caller-visible effects) or `A`'s owned memory: the `frame` bytes below the entry `rsp` (which contain the red zone) and `A.owned` (incoming stack arguments, sret storage) |
| non-vacuity | `nonvacuous`: some admitted call exists |
| partiality | `mode`: `.total` requires a first return from every admitted call; `.ifReturns` constrains only the calls that return (partial correctness) (divergence and getting stuck are then allowed) |

**Machine state the ABI constrains but the machine lacks.** `Ffi.State` has the vector, x87,
direction-flag, MXCSR and x87-control state, and the thread pointer, next to the integer
machine state. `callModelOf M` runs only the integer machine and carries the rest unchanged
(`Thms.callModelOf_carried`), as `Machine.Abi.OpenMachine.callModel` does. So on the integer
machines the control-state obligations of `Return` hold by the model: this is sound because
those machines have no instruction that reads or writes that state (a run that reaches such
an instruction is stuck, so it never returns), and it is stated, not hidden.

**External calls and the runtime.** The machine is the only place behaviour comes from. On
the open machines there are no external calls: a call to code that is not loaded is stuck.
A machine whose steps include trusted callee contracts (`Silmaril.Elf.Link.Dyn.Proc`) makes
those contracts the explicit assumptions of every row stated on it.

**Header satisfaction** (`HeaderSat`): a binary satisfies the part of a header it claims
(`Coverage.claimed`), with every other declaration excluded for a stated reason
(`Exclusion`: unsupported by the ABI fragment, absent from the binary, not claimed);
the claimed functions each have a `Conforms` row. See `docs/projects/abi-conformance.md`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState Word Byte)
open Silmaril.Data.Layout (CTy DataModel)
open Silmaril.Data.Layout.Header (CProto Header)

/-! ## ABI definitions -/

/-- **An ABI definition**: what a conformance statement is judged against. -/
structure AbiDef where
  /-- Versioned identity, e.g. `x86_64-sysv-psabi@e1ce0983/lp64/integer`. -/
  id : String
  /-- The cited document, with its version. -/
  source : String
  /-- Sizes and alignments of C types. -/
  dm : DataModel
  V : Vocab
  D : Type
  /-- Argument placement, return discipline, result read-back. -/
  conv : Convention V Ffi.State D
  /-- The ABI's prototype for a C prototype, or the reason it is outside the ABI fragment. -/
  lower : CProto → Except String V.Proto
  /-- Bytes of the caller's frame the callee receives above its return address (incoming stack
  arguments, a shadow area), which it may read and write. -/
  argArea : V.Proto → Nat
  /-- Other memory the ABI gives the callee at entry `s` (sret storage). -/
  owned : V.Proto → Ffi.State → Nat → Prop

/-! ## The System V AMD64 INTEGER fragment -/

open Silmaril.C.Api (Scalar Signature)

/-- The `C.Api` scalar of a C type under a data model, or why it has none: the fragment has
4- and 8-byte integers and pointers. -/
def scalarOf (dm : DataModel) : CTy → Except String Scalar
  | .typedef _ t => scalarOf dm t
  | .ptr _ => .ok .pointer
  | .int k s => match dm.intShape k with
    | some ⟨4, _⟩ => .ok (if dm.isSigned k s then .int32 else .uint32)
    | some ⟨8, _⟩ => .ok (if dm.isSigned k s then .int64 else .uint64)
    | some ⟨n, _⟩ => .error s!"{n}-byte integer: outside the INTEGER fragment (4- and 8-byte integers and pointers)"
    | none => .error "integer kind without a size in the data model"
  | .bool => .error "_Bool: outside the INTEGER fragment (4- and 8-byte integers and pointers)"
  | .float _ => .error "floating type: SSE/x87 classes are outside the INTEGER fragment"
  | .struct t => .error s!"struct {t} by value: aggregates are outside the INTEGER fragment"
  | .union t => .error s!"union {t} by value: aggregates are outside the INTEGER fragment"
  | .enum t _ => .error s!"enum {t}: enumerations are outside the INTEGER fragment"
  | .array .. => .error "array object type"
  | .void => .error "void object type"

/-- The INTEGER-fragment prototype of a C prototype. -/
def lowerInt (dm : DataModel) (cp : CProto) : Except String Silmaril.Machine.Abi.SystemV.Proto :=
  if cp.variadic then .error "variadic: the %al count and va_list are outside the INTEGER fragment"
  else
    match Silmaril.Data.Layout.traverse (scalarOf dm) cp.params,
        (match cp.ret with
          | .void => (Except.ok none : Except String (Option Scalar))
          | t => some <$> scalarOf dm t) with
    | .error e, _ => .error e
    | _, .error e => .error s!"result: {e}"
    | .ok ps, .ok r =>
      if h : ps.length ≤ Silmaril.Machine.Abi.SystemV.maxArity then .ok ⟨⟨ps, r⟩, h⟩
      else .error "more than 127 parameters"

/-- **System V AMD64, INTEGER fragment**: fixed-arity prototypes of 4- and 8-byte integers and
pointers, planned by the psABI planner (`Machine.SystemV.Abi.plan`, which on this fragment is
`intPlan`), with the full `Ffi.Entry`/`Ffi.Return` discipline (`Machine.Abi.SystemV.sysv`).
Arguments past the sixth are 8-byte stack slots above the return address; the callee owns
that area. -/
def sysvInt : AbiDef where
  id := "x86_64-sysv-psabi@e1ce0983/lp64/integer"
  source := "System V Application Binary Interface, AMD64 Architecture Processor Supplement, \
    x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236, §3.2 (Function Calling \
    Sequence): register save and red zone (§3.2.1–3.2.2), parameter passing (§3.2.3)"
  dm := Silmaril.Data.Layout.sysvX86_64
  V := Silmaril.Machine.Abi.SystemV.vocab
  D := Silmaril.Machine.Abi.SystemV.CallSite
  conv := Silmaril.Machine.Abi.SystemV.sysv {}
  lower := lowerInt Silmaril.Data.Layout.sysvX86_64
  argArea p := 8 * (p.signature.arguments.length - 6)
  owned _ _ _ := False

/-! ## Code, machines, specs -/

/-- **The code of a function**: `bytes` loaded at `base`, entered at offset `off`; the function
itself is the `len` bytes from `off` (its symbol's extent). The other bytes are code it may
reach (a tail call, a shared epilogue). `data` are read-only data of the same image the code
reads at fixed addresses (a constant table); an admitted call has them loaded too. -/
structure Code where
  base : Word
  bytes : List Byte
  off : Nat
  len : Nat
  data : List (Word × List Byte) := []

/-- The entry address. -/
def Code.entry (c : Code) : Word := c.base + BitVec.ofNat 64 c.off

/-- The machines conformance is stated on (`Mach`): x86-64 segment machines on the open state. -/
abbrev Mach := Silmaril.X86.SegVC.Isa MState

/-- **The call relation of `M`**: the first return of the run from the entry state, with the
state the machine does not model (vectors, x87, control state, FFI thread pointer) carried. -/
def callModelOf (M : Mach) : Contracts.Model Ffi.State Ffi.State := fun s =>
  {t | Silmaril.X86.FnContract.FirstReturn M s.machine t.machine ∧ t = { s with machine := t.machine }}

/-- **A C-level call spec** for prototype `p`: a precondition on the arguments and the entry
state (validity of what pointers point to, absence of undefined behaviour), the caller-visible
memory the call may write, and the postcondition on the result and the final state. -/
structure CallSpec (V : Vocab) (p : V.Proto) where
  pre : V.Args p → Ffi.State → Prop
  writes : V.Args p → Ffi.State → Nat → Prop := fun _ _ _ => False
  post : V.Args p → Ffi.State → V.Ret p → Ffi.State → Prop

/-- The spec of ABI conformance alone: every call is admitted, nothing caller-visible is
written, any result. -/
def CallSpec.abiOnly (V : Vocab) (p : V.Proto) : CallSpec V p where
  pre _ _ := True
  post _ _ _ _ := True

/-- A value-level C contract (`Contracts.Contract`, as `Convention.translate` takes) as a spec
that writes nothing. -/
def CallSpec.ofContract {V : Vocab} {p : V.Proto}
    (c : Contracts.Contract (V.Args p) (Option (V.Ret p))) : CallSpec V p where
  pre a _ := c.pre a
  post a _ r _ := c.post a (some r)

inductive Mode where
  | total
  | ifReturns
  deriving DecidableEq, Repr

/-! ## The statement -/

/-- The stack pointer of an FFI state. -/
def sp (s : Ffi.State) : Nat := (s.machine.core.read .rsp).toNat

/-- The code is placed: loaded, `rip` at the entry, the return address outside the bytes. -/
structure Placed (c : Code) (s : Ffi.State) : Prop where
  loaded : Silmaril.X86.Ext.Loaded s.machine.memory c.base c.bytes
  pc : s.machine.core.rip = c.entry
  data : ∀ d ∈ c.data, Silmaril.X86.Ext.Loaded s.machine.memory d.1 d.2
  retOutside : ∀ o, o < c.bytes.length →
    Silmaril.X86.FnContract.retOf s.machine.core s.machine.memory ≠ c.base + BitVec.ofNat 64 o

/-- The stack a call needs: `frame` bytes below `rsp`, the return address and `A`'s argument
area, readable, writable and apart from the code. -/
structure Stack (A : AbiDef) (p : A.V.Proto) (c : Code) (frame : Nat) (s : Ffi.State) : Prop where
  room : frame ≤ sp s
  fits : sp s + 8 + A.argArea p ≤ 2 ^ 64
  read : s.machine.memory.Permitted .read (sp s - frame) (frame + 8 + A.argArea p)
  write : s.machine.memory.Permitted .write (sp s - frame) (frame + 8 + A.argArea p)
  apart : c.base.toNat + c.bytes.length ≤ sp s - frame ∨ sp s + 8 + A.argArea p ≤ c.base.toNat

/-- **An admitted call** of the code with arguments `a`. -/
structure Admit (A : AbiDef) (M : Mach) (p : A.V.Proto) (c : Code) (frame : Nat)
    (a : A.V.Args p) (s : Ffi.State) : Prop where
  live : M.live s.machine
  entry : A.conv.Entry p a s
  placed : Placed c s
  stack : Stack A p c frame s

/-- The memory `A` gives a callee entered at `s`: the `frame` bytes below `rsp` (its frame,
including the red zone), its argument area above the return address, and `A.owned`. -/
def Owned (A : AbiDef) (p : A.V.Proto) (frame : Nat) (s : Ffi.State) (x : Nat) : Prop :=
  (sp s - frame ≤ x ∧ x < sp s) ∨ (sp s + 8 ≤ x ∧ x < sp s + 8 + A.argArea p) ∨ A.owned p s x

/-- **A conforming return** from `s` to `t` for arguments `a`. -/
structure Good (A : AbiDef) (p : A.V.Proto) (frame : Nat) (S : CallSpec A.V p)
    (a : A.V.Args p) (s t : Ffi.State) : Prop where
  ret : A.conv.Return p s t
  result : ∃ r, A.conv.ResultAt p s t r ∧ S.post a s r t
  frame : s.machine.memory.WritesWithin t.machine.memory
    (fun x => S.writes a s x ∨ Owned A p frame s x)

/-- Header source files (name, text) and the file to read. -/
structure HeaderSrc where
  files : List (String × String)
  root : String

/-- The C prototype the header declares for `f`, if the header reads. -/
def HeaderSrc.proto? (hdr : HeaderSrc) (f : String) : Option CProto :=
  (Silmaril.Data.Layout.Header.read hdr.files hdr.root).toOption.bind (·.proto? f)

/-- **The header declares `f` with a C prototype that `A` lowers to `p`.** -/
def Declares (A : AbiDef) (hdr : HeaderSrc) (f : String) (p : A.V.Proto) : Prop :=
  ∃ cp, hdr.proto? f = some cp ∧ A.lower cp = .ok p

/-- **The code conforms to `A` as the function `f` of the header `hdr`**, with prototype `p`,
`frame` bytes of stack and C-level spec `S`, on the machine `M`. -/
structure Conforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop where
  declared : Declares A hdr f p
  extent : c.off + c.len ≤ c.bytes.length
  nonvacuous : ∃ a s, Admit A M p c frame a s ∧ S.pre a s
  progress : mode = .total → ∀ a s, Admit A M p c frame a s → S.pre a s →
    (callModelOf M s).Nonempty
  sound : ∀ a s, Admit A M p c frame a s → S.pre a s →
    ∀ t ∈ callModelOf M s, Good A p frame S a s t

/-! ## Header satisfaction -/

/-- Why a declaration of a header is not claimed for a binary. -/
inductive Exclusion where
  /-- The ABI's lowering refuses the prototype (checked; `why` summarizes `A.lower`'s message). -/
  | unsupported (why : String)
  /-- The binary does not define the function (an API version gap). -/
  | absent (why : String)
  /-- Defined and in the fragment, but not claimed (for instance: the machine model lacks an
  instruction the code uses). -/
  | unclaimed (why : String)
  deriving DecidableEq, Repr

/-- **A coverage declaration** for a header and a binary: the claimed functions, and every
other declared function with its exclusion. -/
structure Coverage where
  claimed : List String
  excluded : List (String × Exclusion)
  deriving DecidableEq, Repr

/-- The coverage accounts for the header: every declared name is claimed or excluded, not both,
and nothing else is listed. -/
def Coverage.Complete (cov : Coverage) (H : Header) : Prop :=
  (∀ f ∈ H.names, f ∈ cov.claimed ∨ f ∈ cov.excluded.map (·.1)) ∧
  (∀ f ∈ cov.claimed, f ∈ H.names ∧ f ∉ cov.excluded.map (·.1)) ∧
  (∀ f ∈ cov.excluded.map (·.1), f ∈ H.names)

instance (cov : Coverage) (H : Header) : Decidable (cov.Complete H) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Every `unsupported` exclusion is refused by the lowering (the stated reason is the
reader's summary of the lowering's message). -/
def Coverage.refusalsOk (A : AbiDef) (cov : Coverage) (H : Header) : Bool :=
  cov.excluded.all fun (f, e) => match e with
    | .unsupported _ => match H.proto? f with
      | some cp => (match A.lower cp with | .error _ => true | .ok _ => false)
      | none => false
    | _ => true

/-- **The coverage is checked against the header** (a computation): the header reads, the
coverage is complete, and the `unsupported` exclusions are refused by the lowering. -/
def Coverage.check (A : AbiDef) (hdr : HeaderSrc) (cov : Coverage) : Bool :=
  match Silmaril.Data.Layout.Header.read hdr.files hdr.root with
  | .ok H => decide (cov.Complete H) && cov.refusalsOk A H
  | .error _ => false

/-- **A binary's functions for a header**: for each claimed name, its code, frame, spec and
mode (the prototype is the header's). -/
structure Impl (A : AbiDef) where
  proto : A.V.Proto
  code : Code
  frame : Nat
  spec : CallSpec A.V proto
  mode : Mode

/-- **The binary satisfies the claimed part of the header**: the coverage is complete, an
unsupported exclusion is refused by the lowering, and every claimed function has an
implementation that conforms. -/
def HeaderSat (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  cov.check A hdr = true ∧
  ∀ f ∈ cov.claimed, ∃ i, impl f = some i ∧
    Conforms A M i.mode hdr f i.proto i.code i.frame i.spec

end Silmaril.Machine.Abi.Conformance

end
