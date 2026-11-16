module

public import Silmaril.Project.Shapes.Consequence.Thms
public import Silmaril.Logic.Consequence.Interp.Thms
public import ProjectSelfTest.Languages

/-!
# The `sil project` self-test: partial interpretations (core `Interp`)

A registry test of partial interpretations, on the registered bytes value
`silmaril.selftest.languages.hello` (`examples/project/data/hello.txt`, the six bytes
`hello\n`). These are test readings of bytes, not Wasm semantics; the Wasm modules through the
protocol track's `coreInterp` are a separate fixture.

* `selftest.prefix_exact` (`Interp ℕ Bytes …`, configuration `n : ℕ`): defined iff the value has
  at most `n` bytes; then `() ⊢ w` iff `w` is a prefix of the value of length exactly `n`. At
  `n = 6` it is defined and accepts `hello\n`; at `n = 100` it is **defined and empty**; at
  `n = 2` it is **undefined** (and the value's bytes do parse).
* `selftest.nonempty_whole` (`Interp₀`, the singleton configuration by default): defined iff the
  value is nonempty; then `() ⊢ w` iff `w` is the whole value.
-/

namespace ProjectSelfTest.Consequence.Partial

open Silmaril.Consequence

@[expose] public section

/-- Defined when the bytes have at most `n` bytes: the prefixes of length exactly `n`. -/
def prefixExact : Interp ℕ Silmaril.Formats.Bytes (fun _ => PUnit.{1}) (fun _ => List UInt8) :=
  fun n b => if b.toList.length ≤ n then some (fun _ w => w <+: b.toList ∧ w.length = n) else none

/-- Defined when the bytes are nonempty: the whole value. -/
def nonemptyWhole : Interp₀ Silmaril.Formats.Bytes PUnit.{1} (List UInt8) :=
  fun _ b => if b.toList = [] then none else some (fun _ w => w = b.toList)

/-- The configuration `6`. -/
def six : ℕ := 6
/-- The configuration `100`. -/
def hundred : ℕ := 100
/-- The configuration `2`. -/
def two : ℕ := 2

theorem prefixExact_orBot (n : ℕ) (b : Silmaril.Formats.Bytes) (u : PUnit.{1}) (w : List UInt8) :
    prefixExact.orBot n b u w ↔ b.toList.length ≤ n ∧ w <+: b.toList ∧ w.length = n := by
  unfold Interp.orBot prefixExact
  by_cases h : b.toList.length ≤ n
  · simp only [h, ↓reduceIte, true_and]; exact Iff.rfl
  · have hn : ¬ b.length ≤ n := by simpa using h
    simp [hn, sysOrBot]

end

end ProjectSelfTest.Consequence.Partial

silmaril consequence_interpretation selftest.prefix_exact := ProjectSelfTest.Consequence.Partial.prefixExact
  (doc := "Test reading of bytes, configuration n : ℕ: defined iff at most n bytes; () ⊢ w iff w is a prefix of length exactly n")
silmaril consequence_interpretation selftest.nonempty_whole := ProjectSelfTest.Consequence.Partial.nonemptyWhole
  (doc := "Test reading of bytes (Interp₀): defined iff nonempty; () ⊢ w iff w is the whole value")

silmaril consequence_system silmaril.selftest.consequence.partial.hello_6 (op := artifact)
  (value := silmaril.selftest.languages.hello) (interpretation := selftest.prefix_exact)
  (env := ProjectSelfTest.Consequence.Partial.six) (title := "hello.txt, prefixes of length exactly 6 (defined)")
silmaril consequence_system silmaril.selftest.consequence.partial.hello_100 (op := artifact)
  (value := silmaril.selftest.languages.hello) (interpretation := selftest.prefix_exact)
  (env := ProjectSelfTest.Consequence.Partial.hundred) (title := "hello.txt, prefixes of length exactly 100 (defined, empty)")
silmaril consequence_system silmaril.selftest.consequence.partial.hello_2 (op := artifact)
  (value := silmaril.selftest.languages.hello) (interpretation := selftest.prefix_exact)
  (env := ProjectSelfTest.Consequence.Partial.two) (title := "hello.txt, at most 2 bytes required (undefined)")
silmaril consequence_system silmaril.selftest.consequence.partial.hello_whole (op := artifact)
  (value := silmaril.selftest.languages.hello) (interpretation := selftest.nonempty_whole)
  (title := "hello.txt, the whole value (Interp₀, default configuration)")

namespace ProjectSelfTest.Consequence.Partial

open Silmaril.Consequence Silmaril.Project.Shapes.Consequence

/-- The value's bytes: six of them, `hello\n`. -/
theorem hello_bytes : silmaril.selftest.languages.hello.Satisfies
    (fun b : Silmaril.Formats.Bytes => b.toList = [104, 101, 108, 108, 111, 10]) :=
  Silmaril.Project.Value.satisfies_of_any (by decide)

end ProjectSelfTest.Consequence.Partial

open ProjectSelfTest.Consequence.Partial Silmaril.Consequence Silmaril.Project.Shapes.Consequence in
section

silmaril instance silmaril.selftest.consequence.partial.defined_6 (expect := THM)
  (title := "hello.txt is read by prefix_exact at 6") := silmaril.shapes.consequence.artifact_defined
  (X := silmaril.selftest.languages.hello) (I := ProjectSelfTest.Consequence.Partial.prefixExact)
  (e := ProjectSelfTest.Consequence.Partial.six)

@[answers "silmaril.selftest.consequence.partial.defined_6" thm]
public theorem defined_6 : ArtifactDefined silmaril.selftest.languages.hello prefixExact six :=
  let ⟨b, hb, h⟩ := hello_bytes
  ⟨b, hb, by simp [Interp.Defined, prefixExact, six, h]⟩

silmaril instance silmaril.selftest.consequence.partial.defined_100 (expect := THM)
  (title := "hello.txt is read by prefix_exact at 100") := silmaril.shapes.consequence.artifact_defined
  (X := silmaril.selftest.languages.hello) (I := ProjectSelfTest.Consequence.Partial.prefixExact)
  (e := ProjectSelfTest.Consequence.Partial.hundred)

@[answers "silmaril.selftest.consequence.partial.defined_100" thm]
public theorem defined_100 : ArtifactDefined silmaril.selftest.languages.hello prefixExact hundred :=
  let ⟨b, hb, h⟩ := hello_bytes
  ⟨b, hb, by simp [Interp.Defined, prefixExact, hundred, h]⟩

silmaril instance silmaril.selftest.consequence.partial.defined_2 (expect := UNS)
  (title := "hello.txt is read by prefix_exact at 2 (fails: 6 bytes > 2)") := silmaril.shapes.consequence.artifact_defined
  (X := silmaril.selftest.languages.hello) (I := ProjectSelfTest.Consequence.Partial.prefixExact)
  (e := ProjectSelfTest.Consequence.Partial.two)

@[answers "silmaril.selftest.consequence.partial.defined_2" csa]
public theorem defined_2 : ¬ ArtifactDefined silmaril.selftest.languages.hello prefixExact two := by
  rintro ⟨b, hb, hd⟩
  obtain ⟨b', hb', h⟩ := hello_bytes
  cases hb.symm.trans hb'
  simp [Interp.Defined, prefixExact, two, h] at hd

silmaril instance silmaril.selftest.consequence.partial.defined_whole (expect := THM)
  (title := "hello.txt is read by nonempty_whole (default configuration)") := silmaril.shapes.consequence.artifact_defined
  (X := silmaril.selftest.languages.hello) (I := ProjectSelfTest.Consequence.Partial.nonemptyWhole)
  (e := PUnit.unit)

@[answers "silmaril.selftest.consequence.partial.defined_whole" thm]
public theorem defined_whole : ArtifactDefined silmaril.selftest.languages.hello nonemptyWhole PUnit.unit :=
  let ⟨b, hb, h⟩ := hello_bytes
  ⟨b, hb, by simp [Interp.Defined, nonemptyWhole, h]⟩

silmaril instance silmaril.selftest.consequence.partial.hello_6_accepts (expect := THM)
  (title := "() ⊢ hello\\n at 6") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.partial.hello_6) (Γ := PUnit.unit) (φ := [104, 101, 108, 108, 111, 10])

@[answers "silmaril.selftest.consequence.partial.hello_6_accepts" thm]
public theorem hello_6_accepts :
    Derives silmaril.selftest.consequence.partial.hello_6 PUnit.unit [104, 101, 108, 108, 111, 10] :=
  let ⟨b, hb, h⟩ := hello_bytes
  ⟨b, hb, (prefixExact_orBot _ _ _ _).2 ⟨by simp [h, six], by simp [h], rfl⟩⟩

silmaril instance silmaril.selftest.consequence.partial.hello_100_empty (expect := UNS)
  (title := "Nothing at 100: defined and empty") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.partial.hello_100)

@[answers "silmaril.selftest.consequence.partial.hello_100_empty" uns]
public theorem hello_100_empty : ∀ Γ φ, ¬ Derives silmaril.selftest.consequence.partial.hello_100 Γ φ := by
  rintro u w ⟨b, hb, hd⟩
  obtain ⟨b', hb', h⟩ := hello_bytes
  cases hb.symm.trans hb'
  obtain ⟨-, hp, hl⟩ := (prefixExact_orBot _ _ _ _).1 hd
  have := hp.length_le
  simp [h, hundred] at this hl
  omega

silmaril instance silmaril.selftest.consequence.partial.hello_2_empty (expect := UNS)
  (title := "Nothing at 2: undefined, read as ⊥ (not a defined empty system)") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.partial.hello_2)

@[answers "silmaril.selftest.consequence.partial.hello_2_empty" uns]
public theorem hello_2_empty : ∀ Γ φ, ¬ Derives silmaril.selftest.consequence.partial.hello_2 Γ φ := by
  rintro u w ⟨b, hb, hd⟩
  obtain ⟨b', hb', h⟩ := hello_bytes
  cases hb.symm.trans hb'
  obtain ⟨hl, -, -⟩ := (prefixExact_orBot _ _ _ _).1 hd
  simp [h, two] at hl

end

silmaril group silmaril.selftest.consequence.partial (title := "Partial interpretations (core Interp), a registry test on bytes")
  (children := [silmaril.selftest.consequence.partial.defined_6,
    silmaril.selftest.consequence.partial.defined_100, silmaril.selftest.consequence.partial.defined_2,
    silmaril.selftest.consequence.partial.defined_whole,
    silmaril.selftest.consequence.partial.hello_6_accepts,
    silmaril.selftest.consequence.partial.hello_100_empty,
    silmaril.selftest.consequence.partial.hello_2_empty])
