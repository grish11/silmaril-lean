module

public import Silmaril.Apps.Sha256sum.Run

/-! # GNU `sha256sum` with file operands: the specification, operand by operand

What `Silmaril.Apps.Sha256sum.sha256sum` says when the command line has no option and at least one
operand, none of them `-` (standard input): the operands are processed in order, each one
independently of the others (`opOut`), and the run's outcome is the concatenation of their outputs
and diagnostics with status 0 exactly when every operand could be read.

* `scanArgs_plain`, `scan_plain`: option scanning on arguments none of which starts with `-` gives
  the default options and the arguments as operands (with or without `POSIXLY_CORRECT`);
* `computeAll_plain`: the per-operand fold (`computeAll`) on operands other than `-`;
* `sha256sum_plain`: the end-to-end form, for a standard output that accepts writes;
* `quotef_plain`: a name of bytes from gnulib's always-safe set (`%+,-./0-9A-Z]_a-z`) is printed
  bare in diagnostics.
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec

open Silmaril.Apps.Sha256sum

/-- What one operand contributes in compute mode: its output line, its diagnostic, and whether it
was read. -/
def opOut (w : World) (o : Opts) (f : Bytes) : Bytes × Bytes × Bool :=
  match w.fs f with
  | .ok data => (computeLine o f data, [], true)
  | .openErr e => ([], diagE w.prog (quotef f) e, false)
  | .readErr e _ => ([], diagE w.prog (quotef f) e, false)

/-- The output of a list of operands. -/
def outs (w : World) (o : Opts) (ops : List Bytes) : Bytes := ops.flatMap fun f => (opOut w o f).1

/-- The diagnostics of a list of operands. -/
def errs (w : World) (o : Opts) (ops : List Bytes) : Bytes := ops.flatMap fun f => (opOut w o f).2.1

/-- Every operand was read. -/
def allOk (w : World) (o : Opts) (ops : List Bytes) : Bool := ops.all fun f => (opOut w o f).2.2

/-- The default options. -/
def opts0 : Opts := {}

/-- An argument that is not an option: it does not start with `-`. -/
def Plain (a : Bytes) : Prop := a.head? ≠ some 45

theorem plain_ne_dash {a : Bytes} (h : Plain a) : a ≠ dash := by
  rintro rfl; exact h rfl

/-- One operand other than `-`. -/
theorem computeOne_plain (w : World) (o : Opts) (st : St) (f : Bytes) (hf : f ≠ dash) :
    computeOne w o st f =
      ({ st with out := st.out ++ (opOut w o f).1, err := st.err ++ (opOut w o f).2.1 }, (opOut w o f).2.2) := by
  unfold computeOne readPath opOut
  simp only [hf, ↓reduceIte]
  cases w.fs f <;> simp [St.emit, St.warn]

/-- **The operand loop of the specification**, on operands other than `-`. -/
theorem computeAll_plain (w : World) (o : Opts) (st : St) (ops : List Bytes) (h : ∀ f ∈ ops, f ≠ dash) :
    computeAll w o st ops =
      ({ st with out := st.out ++ outs w o ops, err := st.err ++ errs w o ops }, allOk w o ops) := by
  induction ops generalizing st with
  | nil => simp [computeAll, outs, errs, allOk]
  | cons f fs ih =>
    simp only [computeAll]
    rw [computeOne_plain w o st f (h f (by simp))]
    rw [ih _ (fun g hg => h g (by simp [hg]))]
    simp [outs, errs, allOk, List.flatMap_cons, List.all_cons, List.append_assoc]

/-- Scanning arguments none of which starts with `-`. -/
theorem scanArgs_plain (prog : Bytes) (posix : Bool) (o : Opts) (acc args : List Bytes)
    (h : ∀ a ∈ args, Plain a) : scanArgs prog posix o acc args = .done o (acc.reverse ++ args) := by
  induction args generalizing acc with
  | nil => simp [scanArgs]
  | cons a rest ih =>
    have ha : Plain a := h a (by simp)
    have hne : a ≠ [45, 45] := by rintro rfl; exact ha rfl
    have ih' := ih (a :: acc) (fun b hb => h b (by simp [hb]))
    rw [scanArgs]; simp only [hne, ↓reduceIte]
    · cases posix
      · simpa using ih'
      · simp
    · intro body hb; exact ha (by simp [hb])
    · intro c cs hb; exact ha (by simp [hb])

theorem scan_plain (prog : Bytes) (posix : Bool) (args : List Bytes) (h : ∀ a ∈ args, Plain a) :
    scan prog posix args = .done opts0 args := by
  simp [scan, scanArgs_plain prog posix {} [] args h, opts0]

/-- **`sha256sum` with plain operands**: no option, at least one operand, none starting with `-`,
and a standard output that accepts writes. The output is each operand's line, in order; the
diagnostics are each unreadable operand's message, in order; the status is 0 iff every operand was
read. -/
theorem sha256sum_plain (w : World) (a0 : Bytes) (ops : List Bytes) (hargv : w.argv = a0 :: ops)
    (hne : ops ≠ []) (hp : ∀ f ∈ ops, Plain f) (hfull : w.stdoutFull = false) :
    sha256sum w = ⟨outs w opts0 ops, errs w opts0 ops, if allOk w opts0 ops then 0 else 1⟩ := by
  have hsc : scan w.argv0 w.posix w.argv.tail = .done opts0 ops := by
    rw [hargv]; exact scan_plain _ _ _ hp
  have hv : validate opts0 = none := by decide
  have hops : operandsOrStdin ops = ops := by simp [operandsOrStdin, hne]
  simp only [sha256sum, hsc, hv, runMode, hops]
  rw [computeAll_plain w opts0 _ ops (fun f hf => plain_ne_dash (hp f hf))]
  have hc : opts0.check = false := rfl
  simp [finish, hfull, hc]

/-! ## `quotef` on plain names -/

/-- gnulib's always-safe bytes never force quoting. -/
theorem needsQuotingAt_safe : ∀ c : UInt8, isSafe c = true →
    ((cEscLetter c).isSome || c == 92 || c == 63 || c == 39 || c == 58 || isShellSpecial c ||
      (c == 35 || c == 126) || (c == 123 || c == 125) || !isPrint c) = false := by
  decide

theorem needsQuoting_safe (s : Bytes) (hs : s ≠ []) (h : ∀ c ∈ s, isSafe c = true) :
    needsQuoting s = false := by
  unfold needsQuoting
  simp only [Bool.or_eq_false_iff, List.isEmpty_eq_false_iff.mpr hs, true_and, List.any_eq_false]
  intro ⟨c, i⟩ hci
  have hc : c ∈ s := (List.mem_zipIdx hci).2.2 ▸ List.getElem_mem _
  have := needsQuotingAt_safe c (h c hc)
  simp only [Bool.or_eq_false_iff] at this
  simp only [needsQuotingAt]
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := this
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- **A name of always-safe bytes is shown bare** in a diagnostic. -/
theorem quotef_plain (s : Bytes) (hs : s ≠ []) (h : ∀ c ∈ s, isSafe c = true) : quotef s = s := by
  simp [quotef, needsQuoting_safe s hs h]

end Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec
