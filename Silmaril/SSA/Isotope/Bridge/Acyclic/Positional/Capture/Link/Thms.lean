module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Ranking
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Trace
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.OpenTrace
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.RenameTrace
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Native

/-! # Checked serial composition at written CFG endpoints

The base linker passes the producer's ordered result to the consumer's
entry. The open linker also supports consumers that retain that result
in their ambient context, by threading it through each local packet.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link

open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (StructuralContext)
open LetCase.Structural.Reply (Γ₀ run)
open Isotope.Semantics (BoundEnv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Rank

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d n m : Nat} {β : BoundCtx τ d} {L K : LCtx τ}

/-- Serial linking passes the global checker, including rows unreachable
from the chosen entry. -/
theorem check (p : Table Φ β L n) (q : Table Φ β K m) (hp : p.check = true) (hq : q.check = true)
    (j : Fin (m + 1)) (a : Operand Φ (β.snoc (packedExitType L)) (q.types j)) :
    (table p q j a).check = true :=
  check_proof p q j a hp hq

/-- Row-zero representatives compose by linking their written rows. -/
def checked (p : CheckedTable Φ β L) (q : Table Φ β K m) (hq : q.check = true)
    (j : Fin (m + 1)) (a : Operand Φ (β.snoc (packedExitType L)) (q.types j)) : CheckedTable Φ β K :=
  ⟨_, table p.table q j a, check p.table q p.checked hq j a, entry p.table q j a 0 p.entry⟩

/-- The written identity contains one dispatch per exit and an empty tail. -/
theorem identity_check (h : L ≠ []) : (identityTable (Φ := Φ) (β := β) h).check = true :=
  ((identityTree h).build .empty).plan.checked

end Rank

section Finite

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d n m : Nat}
  {β : BoundCtx (Ty Empty) d} {L K : LCtx (Ty Empty)}
  (p : Table Φ β L n) (q : Table Φ β K m) (hp : p.check = true) (hq : q.check = true)
  (i : Fin (n + 1)) (j : Fin (m + 1)) (start : Operand Φ β (p.types i))
  (a : Operand Φ (β.snoc (packedExitType L)) (q.types j))

/-- The actual emitter of the linked CFG has the trace of native LetCase
sequencing. The trace retains the original exit tags and primitive order. -/
theorem serial_run (env : BoundEnv (LetCase.Structural.Finite.Value) β) :
    run ((table p q j a).toLetCase (check p q hp hq j a) (leftIndex p q i) (entry p q j a i start)).2 env =
      run (bind (p.toLetCase hp i start) (continuation q j a hq)).2 env :=
  serial_run_proof p q hp hq j a env i start (check p q hp hq j a)

/-- The finite separator reflects the linked computation to native LetCase
sequencing at the exact original and final ordered interfaces. -/
theorem serial_equiv (input : StructuralContext β) :
    Equiv false Γ₀ β
      ((table p q j a).toLetCase (check p q hp hq j a) (leftIndex p q i) (entry p q j a i start)).1
      (bind (p.toLetCase hp i start) (continuation q j a hq)).1 (packedExitType K) :=
  (LetCase.Structural.Finite.equiv_iff_traceArrow_eq input _ _).mpr
    ((LetCase.Structural.Reply.traceArrow_eq_iff_run _ _).mpr (serial_run p q hp hq i j start a))

/-- The actual linked packed SSA region replays to the actual checked
realization of the native LetCase substitution. -/
theorem serial_packed_replay (input : StructuralContext β) :
    let realized := CheckedTable.ofFiniteLetCase input (bind (p.toLetCase hp i start) (continuation q j a hq))
    ReplayEqv false β.toList ((table p q j a).packedSSA (leftIndex p q i) (entry p q j a i start))
      (realized.table.packedSSA 0 realized.entry) [packedExitType K] := by
  let seq := bind (p.toLetCase hp i start) (continuation q j a hq)
  exact ((table p q j a).toLetCase_reify (check p q hp hq j a) (leftIndex p q i) (entry p q j a i start)).trans
    ((reify_equiv_finite _ seq.2 (serial_equiv p q hp hq i j start a input)).trans
      (CheckedTable.ofLetCase_packed_replay (Reverse.exits_ne_nil_of_operand input seq) seq.2).symm)

/-- The decoder identity emits the packet it was given at every inhabited
ordered interface. The entry operand may itself be effectful. -/
theorem identity_equiv (h : L ≠ []) (packet : Operand Φ β (packedExitType L)) :
    Equiv false Γ₀ β ((identityTable h).toLetCase (identity_check h) 0 packet).1 packet.1 (packedExitType L) :=
  identity_equiv_proof h (identity_check h) packet

/-- At a typed packet entry the independently numbered identity represents
that packet's native LetCase class. In particular an input variable gives the
identity class on its open packed interface. -/
theorem nativeClassEquiv_identity (input : StructuralContext β) (h : L ≠ [])
    (packet : Operand Φ β (packedExitType L)) :
    let graph : CheckedTable Φ β L := ⟨_, identityTable h, identity_check h, packet⟩
    Reverse.nativeClassEquiv input (Quotient.mk _ graph) = Quotient.mk _ packet :=
  (Reverse.nativeClassEquiv_mk input _).trans (Quotient.sound (identity_equiv h packet))

/-- Receiving a packet via the written identity emits the native bound
variable at the actual input interface. -/
theorem identity_continuation (h : L ≠ []) :
    Equiv false Γ₀ (β.snoc (packedExitType L))
      (continuation (L := L) (identityTable (Φ := Φ) (β := β) h) 0 ⟨.bv 0, .bv⟩ (identity_check h)).1
      (.bv 0) (packedExitType L) :=
  identity_continuation_proof h (identity_check h)

/-- The output native class depends only on the packed producer class and
the native equation class of the typed receiver. The receiver's table size,
entry label and packet type may all change. -/
theorem checked_congr (input : StructuralContext β) {p₁ p₂ : CheckedTable Φ β L}
    {m₂ : Nat} (q₂ : Table Φ β K m₂) (hq₂ : q₂.check = true)
    (j₂ : Fin (m₂ + 1)) (a₂ : Operand Φ (β.snoc (packedExitType L)) (q₂.types j₂))
    (left : (Reverse.checkedSetoid Φ β L).r p₁ p₂)
    (right : (Reverse.operandSetoid Φ (β.snoc (packedExitType L)) K).r
      (continuation q j a hq) (continuation q₂ j₂ a₂ hq₂)) :
    (Reverse.checkedSetoid Φ β K).r (checked p₁ q hq j a) (checked p₂ q₂ hq₂ j₂ a₂) :=
  checked_congr_proof input (checked p₁ q hq j a) (checked p₂ q₂ hq₂ j₂ a₂) left right
    (serial_equiv p₁.table q p₁.checked hq 0 j p₁.entry a input)
    (serial_equiv p₂.table q₂ p₂.checked hq₂ 0 j₂ p₂.entry a₂ input)

/-- Link a native producer class with a fixed checked receiver. -/
def checkedClass (input : StructuralContext β) :
    Quotient (Reverse.checkedSetoid Φ β L) → Quotient (Reverse.checkedSetoid Φ β K) :=
  Quotient.map (fun producer => checked producer q hq j a)
    (fun {_ _} left => checked_congr q hq j a input q hq j a left (.refl (continuation q j a hq).2.toHasType))

/-- The native class equivalence takes written linking to LetCase substitution. -/
theorem nativeClassEquiv_checkedClass (input : StructuralContext β)
    (producer : Quotient (Reverse.checkedSetoid Φ β L)) :
    Reverse.nativeClassEquiv (L := K) input (checkedClass q hq j a input producer) =
      operandClass (continuation q j a hq) (Reverse.nativeClassEquiv input producer) :=
  Quotient.inductionOn producer fun producer => by
    simp only [checkedClass, operandClass, Quotient.map_mk, Reverse.nativeClassEquiv_mk]
    exact Quotient.sound (serial_equiv producer.table q producer.checked hq 0 j producer.entry a input)

/-- Linking to the independently numbered identity leaves the original
packed producer in its native SSA equation class. -/
theorem checkedClass_identity (input : StructuralContext β) (h : L ≠ [])
    (producer : Quotient (Reverse.checkedSetoid Φ β L)) :
    checkedClass (L := L) (identityTable h) (identity_check h) 0 ⟨.bv 0, .bv⟩ input producer =
      producer := by
  apply (Reverse.nativeClassEquiv (Φ := Φ) (L := L) input).injective
  rw [nativeClassEquiv_checkedClass]
  exact operandClass_identity_proof h (identity_check h) _

end Finite

namespace Open

section Rank

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d n m : Nat} {β : BoundCtx τ d} {L K : LCtx τ}

/-- Every converted row keeps its exact local successor list. -/
theorem carry_localTargets {P : τ} (q : Table Φ (β.snoc P) K m) (i : Fin (m + 1)) :
    (carry q).localTargets i = q.localTargets i :=
  carry_localTargets_proof q i

/-- The packet conversion preserves the global checker result, including
for rows unreachable from the selected entry. -/
theorem carry_check {P : τ} (q : Table Φ (β.snoc P) K m) :
    (carry q).check = q.check :=
  congrArg Rank.check (funext (carry_localTargets q))

theorem check (p : Table Φ β L n) (q : Table Φ (β.snoc (packedExitType L)) K m)
    (hp : p.check = true) (hq : q.check = true)
    (j : Fin (m + 1)) (receive : Operand Φ (β.snoc (packedExitType L)) (q.types j)) :
    (table p q j receive).check = true :=
  Link.check p (carry q) hp ((carry_check q).trans hq) j (carryEntry receive)

/-- Compose actual row-zero representatives at an open receiver interface. -/
def checked (p : CheckedTable Φ β L) (q : CheckedTable Φ (β.snoc (packedExitType L)) K) :
    CheckedTable Φ β K :=
  Link.checked p (carry q.table) ((carry_check q.table).trans q.checked) 0 (carryEntry q.entry)

/-- Ambient weakening leaves the global local-edge graph unchanged. -/
theorem rename_check {e : Nat} {δ : BoundCtx τ e} (r : BoundCtx.Renaming β δ)
    (q : Table Φ β K m) : (renameTable r q).check = q.check :=
  rename_check_proof r q

end Rank

section Finite

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d n m : Nat}
  {β : BoundCtx (Ty Empty) d} {L K : LCtx (Ty Empty)}
  (p : Table Φ β L n) (q : Table Φ (β.snoc (packedExitType L)) K m)
  (hp : p.check = true) (hq : q.check = true) (i : Fin (n + 1)) (j : Fin (m + 1))
  (entry : Operand Φ β (p.types i)) (receive : Operand Φ (β.snoc (packedExitType L)) (q.types j))

/-- The actual linked emitter preserves both original stages, including
reads of the intermediate result after local transfers in the consumer. -/
theorem serial_run (env : BoundEnv LetCase.Structural.Finite.Value β) :
    run ((table p q j receive).toLetCase (check p q hp hq j receive)
      (Link.leftIndex p (carry q) i) (start p q j receive i entry)).2 env =
      run (bind (p.toLetCase hp i entry) (q.toLetCase hq j receive)).2 env :=
  (Link.serial_run p (carry q) hp ((carry_check q).trans hq) i j entry (carryEntry receive) env).trans
    (congrArg (fun k => run (p.toLetCase hp i entry).2 env >>= k)
      (funext (continuation_carry_run_proof q hq ((carry_check q).trans hq) j receive env)))

/-- Reflect the staged sequencing equation into native LetCase at the original
input and ordered outward interface. -/
theorem serial_equiv (input : StructuralContext β) :
    Equiv false Γ₀ β
      ((table p q j receive).toLetCase (check p q hp hq j receive)
        (Link.leftIndex p (carry q) i) (start p q j receive i entry)).1
      (bind (p.toLetCase hp i entry) (q.toLetCase hq j receive)).1 (packedExitType K) :=
  (LetCase.Structural.Finite.equiv_iff_traceArrow_eq input _ _).mpr
    ((LetCase.Structural.Reply.traceArrow_eq_iff_run _ _).mpr (serial_run p q hp hq i j entry receive))

/-- The literal linked CFG and the checked realization of staged sequencing
agree by native replay at the original packed endpoints. -/
theorem serial_packed_replay (input : StructuralContext β) :
    let seq := bind (p.toLetCase hp i entry) (q.toLetCase hq j receive)
    let realized := CheckedTable.ofFiniteLetCase input seq
    ReplayEqv false β.toList
      ((table p q j receive).packedSSA (Link.leftIndex p (carry q) i) (start p q j receive i entry))
      (realized.table.packedSSA 0 realized.entry) [packedExitType K] := by
  let seq := bind (p.toLetCase hp i entry) (q.toLetCase hq j receive)
  exact ((table p q j receive).toLetCase_reify (check p q hp hq j receive)
    (Link.leftIndex p (carry q) i) (start p q j receive i entry)).trans
    ((reify_equiv_finite _ seq.2 (serial_equiv p q hp hq i j entry receive input)).trans
      (CheckedTable.ofLetCase_packed_replay (Reverse.exits_ne_nil_of_operand input seq) seq.2).symm)

/-- Native weakening below the newest slot preserves its trace and the
older ambient values. -/
theorem underBinder_run {X Y A : Ty Empty} (b : Operand Φ (β.snoc Y) A)
    (env : BoundEnv LetCase.Structural.Finite.Value β)
    (x : LetCase.Structural.Finite.Value X) (y : LetCase.Structural.Finite.Value Y) :
    run (b.2.underBinder (X := X)) ((env.snoc x).snoc y) = run b.2 (env.snoc y) :=
  underBinder_run_proof b env x y

/-- Adding an unused older binding keeps the actual emitter's run, with
the newest intermediate packet and older ambient captures in place. -/
theorem weaken_receiver_run {X Y : Ty Empty}
    (q : Table Φ (β.snoc Y) K m) (hq : q.check = true)
    (j : Fin (m + 1)) (a : Operand Φ (β.snoc Y) (q.types j))
    (env : BoundEnv LetCase.Structural.Finite.Value β)
    (source : LetCase.Structural.Finite.Value X) (value : LetCase.Structural.Finite.Value Y) :
    let r := (BoundCtx.Renaming.succ β X).up Y
    run ((renameTable r q).toLetCase ((rename_check r q).trans hq) j ⟨_, a.2.rename r⟩).2
      ((env.snoc source).snoc value) = run (q.toLetCase hq j a).2 (env.snoc value) :=
  weaken_receiver_run_proof q hq _ j a env source value

end Finite

end Open

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link
