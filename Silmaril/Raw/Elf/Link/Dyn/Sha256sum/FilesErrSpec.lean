module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiSpec

/-! # GNU `sha256sum F1 … Fn` with operands that cannot be opened: the specification

The file-error tier: every operand either opens and reads without error and is printed verbatim
(`Verbatim`), or is refused at `open` with some `errno` and consists of gnulib's always-safe
bytes only (`SafeName`: `quotef` shows it bare, so the diagnostic is `prog: NAME: strerror\n` with
the name verbatim). On such a world (PROVED, standard axioms):

* `sha256sum_mixed`: `sha256sum w` = the records of the readable operands in order on standard
  output, the diagnostics `prog: NAME: strerror(e)\n` of the refused ones in order on standard
  error, status 0 iff no operand was refused;
* `progName_noSlash`: with `argv[0]` free of `/`, the program name of the diagnostics is
  `argv[0]` itself (gnulib's `set_program_name` changes nothing).

Restriction (stated, not lifted): refused names are made of the bytes `% + , - . / 0-9 A-Z ] _ a-z`
only (no quoting by `quotef`); readable names contain no backslash, LF or CR (no escaping).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec

open Silmaril.Apps.Sha256sum

/-- **A refused name shown bare**: not empty and made of gnulib's always-safe bytes. -/
structure SafeName (f : Bytes) : Prop where
  ne : f ≠ []
  safe : ∀ c ∈ f, isSafe c = true

/-- An operand of the file-error tier: readable and printed verbatim, or refused at `open` and
shown bare. -/
def MixedOp (w : World) (f : Bytes) : Prop :=
  (Verbatim f ∧ ∃ d, w.fs f = .ok d) ∨ (Plain f ∧ SafeName f ∧ ∃ e, w.fs f = .openErr e)

/-- What one operand of the tier contributes: (record, diagnostic, read). -/
def mixedOut (w : World) (f : Bytes) : Bytes × Bytes × Bool :=
  match w.fs f with
  | .ok d => (fileLine f d, [], true)
  | .openErr e => ([], diagE w.prog f e, false)
  | .readErr e _ => ([], diagE w.prog f e, false)

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by simp only [List.flatMap_cons, h x (by simp), flatMap_congr' l (fun y hy => h y (by simp [hy]))]

theorem all_congr' {α : Type} {f g : α → Bool} : ∀ l : List α, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by simp only [List.all_cons, h x (by simp), all_congr' l (fun y hy => h y (by simp [hy]))]

theorem opOut_mixed {w : World} {f : Bytes} (h : MixedOp w f) : opOut w opts0 f = mixedOut w f := by
  rcases h with ⟨hv, d, hd⟩ | ⟨-, hs, e, he⟩
  · simp only [opOut, mixedOut, hd, computeLine_verbatim f d hv.noProblem]
  · simp only [opOut, mixedOut, he, quotef_plain f hs.ne hs.safe]

/-- **`sha256sum F1 … Fn` on the file-error tier.** -/
theorem sha256sum_mixed (w : World) (a0 : Bytes) (ops : List Bytes) (hargv : w.argv = a0 :: ops)
    (hne : ops ≠ []) (hop : ∀ f ∈ ops, MixedOp w f) (hfull : w.stdoutFull = false) :
    sha256sum w = ⟨ops.flatMap (fun f => (mixedOut w f).1), ops.flatMap (fun f => (mixedOut w f).2.1),
      if ops.all (fun f => (mixedOut w f).2.2) then 0 else 1⟩ := by
  have hp : ∀ f ∈ ops, Plain f := fun f hf => by
    rcases hop f hf with ⟨hv, -⟩ | ⟨hp, -⟩
    · exact hv.plain
    · exact hp
  rw [sha256sum_plain w a0 ops hargv hne hp hfull]
  have e1 : outs w opts0 ops = ops.flatMap (fun f => (mixedOut w f).1) :=
    flatMap_congr' ops fun f hf => by rw [opOut_mixed (hop f hf)]
  have e2 : errs w opts0 ops = ops.flatMap (fun f => (mixedOut w f).2.1) :=
    flatMap_congr' ops fun f hf => by rw [opOut_mixed (hop f hf)]
  have e3 : allOk w opts0 ops = ops.all (fun f => (mixedOut w f).2.2) := by
    unfold allOk
    exact all_congr' ops fun f hf => by rw [opOut_mixed (hop f hf)]
  rw [e1, e2, e3]

theorem takeWhile_all {p : UInt8 → Bool} : ∀ l : List UInt8, (∀ c ∈ l, p c = true) → l.takeWhile p = l
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.takeWhile_cons, h x (by simp), ↓reduceIte, takeWhile_all l (fun c hc => h c (by simp [hc]))]

/-- With `argv[0]` free of `/`, the program name is `argv[0]`. -/
theorem progName_noSlash (a0 : Bytes) (h : (47 : UInt8) ∉ a0) : progName a0 = a0 := by
  have hb : (a0.reverse.takeWhile (· != 47)).reverse = a0 := by
    rw [takeWhile_all _ (fun c hc => by
      have : c ≠ 47 := fun he => h (he ▸ List.mem_reverse.mp hc)
      simpa using this), List.reverse_reverse]
  simp only [progName, hb, Nat.sub_self, List.take_zero]
  rfl

end Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec
