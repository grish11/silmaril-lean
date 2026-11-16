module

public import Silmaril.Wasi.IOAccept.Thms
public import Silmaril.Semantics.Accept.Success.Thms

/-! # Relational I/O acceptance of component traces: worked examples

Components built with `Strategy.generate`, values encoded as `u32`:

* `echo`: the export `run: func()` calls the import `input: func() -> u32`, receives `a`, calls
  the import `output(a)` and returns. Input `a` triggers `a` and has the episode `([a], ())`;
  an input triggers no other output (`echo_triggers`), because every output of a play is
  issued after the only input of its call.
* `echoTrap`: the same, but the export call traps (`ret … none`) at the end: the output is
  still triggered, but there is no episode (`echoTrap_not_returns`).
* `checked`: the export `f(x) -> result<u32>` returns `ok(x)` for `x ≠ 0` and `error` for `0`;
  its classic input/return relation restricted to successful values (`inlVals`, the `ok`
  side of `Silmaril.Accept.succ`) relates `x` to `x` for `x ≠ 0` and `0` to nothing.
-/

@[expose] public section

namespace Silmaril.Wasi.IOAcceptExamples

open Silmaril.Games Silmaril.Accept Silmaril.Accept.IO Silmaril.Wasi Silmaril.Wasi.IOAccept
open Silmaril.Wasm.Component (Val)
open scoped Silmaril.Accept List

/-! ## Plays of generated strategies -/

/-- A Proponent move of a generated strategy's play, preceded by another move, comes with it from
one generator: the Opponent move `generate` may add is last. -/
theorem pair_mem_generate {E F : Sig.{0}} {S : Set (List (Move E F))}
    {p : List (Move E F)} (hp : p ∈ Strategy.generate S) {m₁ m₂ : Move E F}
    (h : [m₁, m₂] <+ p) (hP : m₂.IsP) : ∃ s ∈ S, m₁ ∈ s ∧ m₂ ∈ s := by
  obtain ⟨-, s, hs, hpre⟩ := hp
  have key : ∀ {q}, q <+: s → [m₁, m₂] <+ q → ∃ s ∈ S, m₁ ∈ s ∧ m₂ ∈ s := by
    intro q hq h
    rcases hs with rfl | ⟨hs, -⟩
    · rw [List.prefix_nil.1 hq] at h; simp at h
    · exact ⟨s, hs, hq.subset (h.subset List.mem_cons_self),
        hq.subset (h.subset (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  rcases hpre with hpre | ⟨p₀, o, rfl, hp₀, ho⟩
  · exact key hpre h
  · refine key hp₀ ?_
    obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.1 h
    rcases List.sublist_singleton.1 h₂ with rfl | rfl
    · rw [List.append_nil] at he
      rw [he]
      exact h₁
    · have : m₂ = o := by
        have := congrArg List.getLast? he
        simpa using this
      exact absurd (this ▸ ho) (Move.not_isO_of_isP hP)

/-- A pair of named events of a play comes from a pair of moves. -/
theorem pair_moves {E F : Set FnName} {s : List (Move (nsig E) (nsig F))} {e₁ e₂ : WEv}
    (h : [e₁, e₂] <+ wtrace s) :
    ∃ m₁ m₂, [m₁, m₂] <+ s ∧ wev m₁ = e₁ ∧ wev m₂ = e₂ := by
  obtain ⟨l, hl, he⟩ := List.sublist_map_iff.1 h
  match l, he with
  | [m₁, m₂], he =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    exact ⟨m₁, m₂, hl, he.1.symm, he.2.symm⟩

/-- Import calls and export returns are Proponent moves. -/
theorem isP_of_wev {E F : Set FnName} {m : Move (nsig E) (nsig F)}
    (h : (∃ f a, wev m = .req f a) ∨ ∃ f a r, wev m = .ret f a r) : m.IsP := by
  rcases m with (_ | _) | (_ | _) <;> simp_all [wev, Move.IsP]

/-! ## The echo component -/

/-- The export `run`. -/
def runFn : FnName := ⟨"echo", "run"⟩
/-- The import `input: func() -> u32`. -/
def inputFn : FnName := ⟨"echo", "input"⟩
/-- The import `output: func(u32)`. -/
def outputFn : FnName := ⟨"echo", "output"⟩

/-- The imports. -/
abbrev Im : Set FnName := {inputFn, outputFn}
/-- The exports. -/
abbrev Ex : Set FnName := {runFn}

/-- A single `u32` value. -/
def u32? : List Val → Option (BitVec 32)
  | [.u32 x] => some x
  | _ => none

/-- Input through the answer of `input`, output through the argument of `output`. -/
abbrev ρ : Roles Unit (BitVec 32) (BitVec 32) Unit := importIO inputFn outputFn u32? u32?

/-- The call of `run`. -/
def runQ : (nsig Ex).Op := (⟨runFn, rfl⟩, [])
/-- The call of `input`. -/
def inQ : (nsig Im).Op := (⟨inputFn, .inl rfl⟩, [])
/-- The call of `output(v)`. -/
def outQ (v : BitVec 32) : (nsig Im).Op := (⟨outputFn, .inr rfl⟩, [.u32 v])

/-- `run` is called; `input()` answers `v`; `output(v)` is called and answered; `run` ends with
`res` (`some []`: returns; `none`: traps). -/
def echoPlay (res : Option (List Val)) (v : BitVec 32) : List (Move (nsig Im) (nsig Ex)) :=
  [.inr (.ask runQ), .inl (.ask inQ), .inl (.ans inQ (some [.u32 v])), .inl (.ask (outQ v)),
   .inl (.ans (outQ v) (some [])), .inr (.ans runQ res)]

theorem echoPlay_legal (res : Option (List Val)) (v : BitVec 32) : Legal (echoPlay res v) :=
  ⟨_, .cons (.ask _) (.cons (.call _ _) (.cons (.reply _ _ _) (.cons (.call _ _)
    (.cons (.reply _ _ _) (.cons (.ret _ _) (.nil _))))))⟩

/-- The echo component. -/
def echo : Strategy (nsig Im) (nsig Ex) := Strategy.generate {s | ∃ v, s = echoPlay (some []) v}

/-- The trapping echo component. -/
def echoTrap : Strategy (nsig Im) (nsig Ex) := Strategy.generate {s | ∃ v, s = echoPlay none v}

/-- The decoded runs of the echo play. -/
theorem inputRuns_echoPlay (res : Option (List Val)) (v : BitVec 32) :
    inputRuns (decode (tag ρ) (wtrace (echoPlay res v))) = [⟨v, [v], res.map fun _ => ()⟩] := by
  cases res <;> rfl

theorem run_mem_echo (v : BitVec 32) : ⟨v, [v], some ()⟩ ∈ ioRuns echo ρ :=
  ⟨_, ⟨_, ⟨_, Strategy.subset_generate ⟨v, rfl⟩ (echoPlay_legal _ _), rfl⟩, rfl⟩,
    by rw [inputRuns_echoPlay]; exact List.mem_singleton_self _⟩

theorem run_mem_echoTrap (v : BitVec 32) : ⟨v, [v], none⟩ ∈ ioRuns echoTrap ρ :=
  ⟨_, ⟨_, ⟨_, Strategy.subset_generate ⟨v, rfl⟩ (echoPlay_legal _ _), rfl⟩, rfl⟩,
    by rw [inputRuns_echoPlay]; exact List.mem_singleton_self _⟩

/-- Input `a` triggers output `a`. -/
example (a : BitVec 32) : (a, a) ∈ triggers (ioRuns echo ρ) :=
  mem_triggers_of_run (run_mem_echo a) List.mem_cons_self

/-- Input `a` has the episode: output `[a]`, then return. -/
example (a : BitVec 32) : (a, ([a], ())) ∈ episodes (ioRuns echo ρ) := run_mem_echo a

/-- The decoded events of the echo play. -/
theorem echoPlay_events {res : Option (List Val)} {v : BitVec 32} {e : WEv}
    (he : e ∈ wtrace (echoPlay res v)) :
    (∀ a, locOf ρ e = some (.inp a) → a = v) ∧ (∀ b, locOf ρ e = some (.out b) → b = v) ∧
      ∀ f a r, e = .ret f a (some r) → res = some r := by
  simp only [wtrace, echoPlay, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> cases res <;>
    simp [wev, locOf, tag, importIO, inQ, outQ, runQ, u32?, tagLoc, inputFn, outputFn]

/-- **No input triggers another output**: in every play of `echo`, the only output of a call
follows its only input. -/
theorem echo_triggers {a b : BitVec 32} (h : (a, b) ∈ triggers (ioRuns echo ρ)) : a = b := by
  obtain ⟨s, hs, e₁, e₂, hsub, h₁, h₂⟩ := triggers_ioRuns_sound h
  obtain ⟨m₁, m₂, hm, rfl, rfl⟩ := pair_moves hsub
  obtain ⟨f, args, hreq, -⟩ := locOf_eq_out h₂
  obtain ⟨_, ⟨v, rfl⟩, hm₁, hm₂⟩ := pair_mem_generate hs hm (isP_of_wev (.inl ⟨f, args, hreq⟩))
  rw [(echoPlay_events (List.mem_map_of_mem hm₁)).1 a h₁,
    (echoPlay_events (List.mem_map_of_mem hm₂)).2.1 b h₂]

/-- The trapped call still triggers its output. -/
example (a : BitVec 32) : (a, a) ∈ triggers (ioRuns echoTrap ρ) :=
  mem_triggers_of_run (run_mem_echoTrap a) List.mem_cons_self

/-- **A trapped call has no episode**: no input returns. -/
theorem echoTrap_not_returns (a : BitVec 32) (c : Unit) : (a, c) ∉ returns (ioRuns echoTrap ρ) := by
  intro h
  obtain ⟨s, hs, e₁, e₂, hsub, -, h₂⟩ := returns_ioRuns_sound h
  obtain ⟨m₁, m₂, hm, rfl, rfl⟩ := pair_moves hsub
  obtain ⟨f, args, r, hret, -⟩ := locOf_eq_exit h₂
  obtain ⟨_, ⟨v, rfl⟩, -, hm₂⟩ :=
    pair_mem_generate hs hm (isP_of_wev (.inr ⟨f, args, _, hret⟩))
  cases (echoPlay_events (List.mem_map_of_mem hm₂)).2.2 f args r hret

example (a : BitVec 32) (bs : List (BitVec 32)) (c : Unit) :
    (a, (bs, c)) ∉ episodes (ioRuns echoTrap ρ) :=
  fun h => echoTrap_not_returns a c ⟨bs, h⟩

/-! ## The export reading: `f(x) -> result<u32>` -/

/-- The export `f`. -/
def fFn : FnName := ⟨"checked", "f"⟩

/-- `ok(x)`. -/
def okV (x : BitVec 32) : Val := .variant 0 (some (.u32 x))
/-- `error`. -/
def errV : Val := .variant 1 none

/-- A `result<u32>` value: `inl` for `ok`, `inr` for `error`. -/
def result? : List Val → Option (BitVec 32 ⊕ Unit)
  | [.variant 0 (some (.u32 y))] => some (.inl y)
  | [.variant 1 none] => some (.inr ())
  | _ => none

/-- The call `f(x)` returning `r`. -/
def fPlay (x : BitVec 32) (r : Val) : List (Move (nsig ∅) (nsig {fFn})) :=
  [.inr (.ask (⟨fFn, rfl⟩, [.u32 x])), .inr (.ans (⟨fFn, rfl⟩, [.u32 x]) (some [r]))]

/-- `f(x)` returns `ok(x)` for `x ≠ 0` and `error` for `0`. -/
def checked : Strategy (nsig ∅) (nsig {fFn}) :=
  Strategy.generate ({s | ∃ x, x ≠ 0 ∧ s = fPlay x (okV x)} ∪ {fPlay 0 errV})

/-- The entry reading of `f`. -/
abbrev ρf : Roles (BitVec 32) Empty Empty (BitVec 32 ⊕ Unit) := exportFn fFn u32? result?

/-- The classic input/return relation, restricted to successful (`ok`) values. -/
abbrev okReturns : BitVec 32 -|> BitVec 32 := inlVals (returns (entryIORuns checked ρf))

theorem fPlay_legal (x : BitVec 32) (r : Val) : Legal (fPlay x r) :=
  ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩

example (x : BitVec 32) (hx : x ≠ 0) : (x, x) ∈ okReturns :=
  mem_inlVals.2 ⟨[], _, ⟨_, ⟨_, Strategy.subset_generate (.inl ⟨x, hx, rfl⟩) (fPlay_legal _ _),
    rfl⟩, rfl⟩, by rw [show entryRuns (decode (tag ρf) (wtrace (fPlay x (okV x)))) =
      [⟨x, [], some (.inl x)⟩] from rfl]; exact List.mem_singleton_self _⟩

/-- `f(0)` returns `error`... -/
example : ((0 : BitVec 32), Sum.inr ()) ∈ returns (entryIORuns checked ρf) :=
  ⟨[], _, ⟨_, ⟨_, Strategy.subset_generate (.inr rfl) (fPlay_legal _ _), rfl⟩, rfl⟩,
    by rw [show entryRuns (decode (tag ρf) (wtrace (fPlay 0 errV))) =
      [⟨0, [], some (.inr ())⟩] from rfl]; exact List.mem_singleton_self _⟩

/-- ...so `0` has no successful value. -/
example (y : BitVec 32) : ((0 : BitVec 32), y) ∉ okReturns := by
  intro h
  obtain ⟨s, hs, e₁, e₂, hsub, h₁, h₂⟩ := returns_entryIORuns_sound (mem_inlVals.1 h)
  obtain ⟨m₁, m₂, hm, rfl, rfl⟩ := pair_moves hsub
  obtain ⟨f, args, r, hret, hr⟩ := locOf_eq_exit h₂
  obtain ⟨g, hg, hm₁, hm₂⟩ := pair_mem_generate hs hm (isP_of_wev (.inr ⟨f, args, _, hret⟩))
  rcases hg with ⟨x, hx, rfl⟩ | hg
  · simp only [fPlay, List.mem_cons, List.not_mem_nil, or_false] at hm₁
    rcases hm₁ with rfl | rfl
    · simp [wev, locOf, tag, exportFn, u32?, tagLoc] at h₁
      exact hx h₁
    · simp [wev, locOf, tag, tagLoc] at h₁
  · rw [Set.mem_singleton_iff.1 hg] at hm₂
    simp only [fPlay, List.mem_cons, List.not_mem_nil, or_false] at hm₂
    rcases hm₂ with rfl | rfl
    · simp [wev] at hret
    · simp only [wev, WEv.ret.injEq, Option.some.injEq] at hret
      obtain ⟨rfl, rfl, rfl⟩ := hret
      simp [exportFn, errV, result?] at hr

end Silmaril.Wasi.IOAcceptExamples
