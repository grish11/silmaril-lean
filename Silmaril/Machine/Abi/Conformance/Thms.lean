module

public import Silmaril.Machine.Abi.Conformance.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.Basic

/-! # ABI conformance: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.Basic`:

* `conforms_of_strict`: **the bridge from function contracts**: a first-return contract
  (`FnContract.Spec.Strict`) of the code on `M`, whose entry every admitted call meets and whose
  results are conforming returns, gives a `Conforms` row (total and partial-correctness);
* `Conforms.exists_good`: a total row has an admitted call with a conforming return (so it is
  not vacuous);
* `Conforms.weaken`, `Conforms.toPartial`: weaker postconditions, larger write sets, and the
  partial-correctness mode follow;
* `callModelOf_carried`: the call relation carries the state the integer machine lacks (vectors,
  x87, direction flag, MXCSR, x87 control word, FFI thread pointer), which is why those
  obligations of `Return` hold by the model on the integer machines;
* `HeaderSat.conforms`: a header satisfaction gives each claimed function's row;
* `sysvInt_lower_examples`: what the INTEGER fragment lowers and refuses, and that a coverage's
  `unsupported` exclusions are checked against the lowering.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState)
open Silmaril.X86.FnContract (Spec AbiEntry)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {c : Code} {frame : Nat} {S : CallSpec A.V p}

theorem conforms_of_strict {S' : Spec MState} (hs : S'.Strict M)
    (hdecl : Declares A hdr f p) (hext : c.off + c.len ≤ c.bytes.length)
    (hnv : ∃ a s, Admit A M p c frame a s ∧ S.pre a s)
    (habi : ∀ a s, Admit A M p c frame a s → AbiEntry (M.core s.machine) (M.mem s.machine))
    (hentry : ∀ a s, Admit A M p c frame a s → S.pre a s → S'.entry s.machine)
    (hgood : ∀ a s t, Admit A M p c frame a s → S.pre a s → S'.Result M s.machine t →
      Good A p frame S a s { s with machine := t }) :
    Conforms A M mode hdr f p c frame S :=
  Silmaril.Proofs.Machine.Abi.Conformance.conforms_of_strict hs hdecl hext hnv habi hentry hgood

theorem Conforms.exists_good (h : Conforms A M .total hdr f p c frame S) :
    ∃ a s t, Admit A M p c frame a s ∧ t ∈ callModelOf M s ∧ Good A p frame S a s t :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.exists_good h

theorem Conforms.weaken {S₂ : CallSpec A.V p} (h : Conforms A M mode hdr f p c frame S)
    (hpre : ∀ a s, S₂.pre a s ↔ S.pre a s)
    (hpost : ∀ a s r t, S.pre a s → S.post a s r t → S₂.post a s r t)
    (hw : ∀ a s x, S.writes a s x → S₂.writes a s x) :
    Conforms A M mode hdr f p c frame S₂ :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.weaken h hpre hpost hw

theorem Conforms.toPartial (h : Conforms A M .total hdr f p c frame S) :
    Conforms A M .ifReturns hdr f p c frame S :=
  Silmaril.Proofs.Machine.Abi.Conformance.Conforms.toPartial h

theorem callModelOf_carried {s t : Ffi.State} (h : t ∈ callModelOf M s) :
    t.vectors = s.vectors ∧ t.x87 = s.x87 ∧ t.direction = s.direction ∧ t.x87Mode = s.x87Mode ∧
      t.mxcsr = s.mxcsr ∧ t.x87Control = s.x87Control ∧ t.fsBase = s.fsBase := by
  rw [h.2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The INTEGER fragment's lowering, on examples -/

/-- What `sysvInt` lowers and refuses, and a coverage with an `unsupported` exclusion. -/
theorem sysvInt_lower_examples :
    (sysvInt.lower ⟨.int .long .unsigned, [.ptr .void, .int .int .signed], false⟩).toOption.map
        (·.signature) = some ⟨[.pointer, .int32], some .uint64⟩ ∧
    (sysvInt.lower ⟨.void, [.int .size .unsigned], false⟩).toOption.map (·.signature) =
      some ⟨[.uint64], none⟩ ∧
    (sysvInt.lower ⟨.float .double, [.float .double], false⟩).toOption.isNone = true ∧
    (sysvInt.lower ⟨.int .int .signed, [.struct "s"], false⟩).toOption.isNone = true ∧
    (sysvInt.lower ⟨.int .int .signed, [.int .short .signed], false⟩).toOption.isNone = true ∧
    (sysvInt.lower ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩).toOption.isNone = true ∧
    Coverage.check sysvInt ⟨[("h.h", "double f(double); int g(int); int printf(const char *, ...);")], "h.h"⟩
      ⟨[], [("f", .unsupported "SSE"), ("g", .unclaimed "example"),
        ("printf", .unsupported "varargs")]⟩ = true ∧
    Coverage.check sysvInt ⟨[("h.h", "double f(double); int g(int);")], "h.h"⟩
      ⟨[], [("f", .unsupported "SSE"), ("g", .unsupported "wrong")]⟩ = false := by
  decide +kernel

theorem HeaderSat.conforms {cov : Coverage} {impl : String → Option (Impl A)}
    (h : HeaderSat A M hdr cov impl) {f : String} (hf : f ∈ cov.claimed) :
    ∃ i, impl f = some i ∧ Conforms A M i.mode hdr f i.proto i.code i.frame i.spec :=
  h.2 f hf

end Silmaril.Machine.Abi.Conformance

end
