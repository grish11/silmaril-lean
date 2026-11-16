module

public import Silmaril.Proofs.Sim.X86.Toy.Main

/-!
# The toy `f`: the Wasm problem, the x86 problem

* **`wasm_solution`**: the Wasm problem of `f` (`LProblemM`), from `toy_entries` by the
  dispatcher's cut-point rule `dispatch_hwp`;
* **`x86_solution`**: the x86 problem (`XLProblemM (toyTab b) (toyWin sp) …`), by
  `xlproblemM_of_lproblemM`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Toy

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State MState)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GM Silmaril.Sim.X86.Loop
open Silmaril.Sim.X86.SumTo (tri)
open Silmaril.Wasm.Logic.Core (exec Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem supported (b sp : Word) : SupportedM (toyWin sp) (toyTab b) := by
  intro e he
  simp only [toyTab, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The first cut point from the hypotheses of the Wasm problem. -/
theorem jt_init {s : Store H} {f : Frame} {R : Reg → Word} {b sp w ret : Word} {B : ByteArray}
    (hG : GRegs s f R) (hw : gval s f .rip = some (Val.i64 w)) (hB : wbytes s f = some B)
    (hsz : (toyWin sp).size ≤ B.size) (hw' : w = b + 0x1d) (hsp : R .rsp = sp)
    (hret : Ld B 32 ret) : JT b sp ret f R (5 * (R .rdi).toNat + 29) s := by
  obtain ⟨hl, hr, -, -, ⟨bz, hz⟩, -, -⟩ := hG
  subst hw'
  refine ⟨_, R .rax, R .rdi, sp, R .rbx, R .r12, b64 bz, B,
    ⟨hl, hw, hr _, hr _, by rw [hr, hsp], hr _, hr _, hz, fun r _ _ _ _ _ => hr r, hB, hsz⟩, ?_⟩
  dsimp only [CP]
  exact ⟨hret, .inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **The Wasm problem of `f` is solved** (every profile, every host relation). -/
theorem wasm_solution (b sp : Word) :
    LProblemM (H := H) P host (toyWin sp) (dispCode (compileTabM (toyWin sp) (toyTab b)))
      (ToyPre b sp) ToyPost := by
  intro s f R w B hG hw hB hsz hpre
  obtain ⟨hw', hsp, h32, h8, ret, hret, hdist⟩ := hpre
  have hJ := jt_init hG hw hB hsz hw' hsp hret
  refine dispatch_hwp _ (fun s => ∃ k, JT b sp ret f R k s) _ ?_ ⟨_, hJ⟩
  rintro s' ⟨k, hk⟩
  obtain ⟨w', hw'', hm⟩ := toy_entries b sp ret R h32 h8 hdist k s' hk
  refine ⟨w', hw'', ?_⟩
  revert hm
  cases lookupC (compileTabM (toyWin sp) (toyTab b)) w' with
  | some code =>
    rintro ⟨s'', he, k', -, hk'⟩
    exact ⟨s'', he, k', hk'⟩
  | none =>
    rintro ⟨-, di, zf, B', hl, hip, hax, -, hsp', hbx, hr12, -, hoth, -⟩
    refine ⟨rfl, fun R' w'' hR' hw''' => ⟨?_, ?_, fun r h1 h2 h3 => ?_, ?_⟩⟩
    · have := hR' .rax
      rw [hax, Option.some.injEq, val_i64_inj] at this
      rw [← this]; bv_omega
    · have := hR' .rsp
      rw [hsp', Option.some.injEq, val_i64_inj] at this
      rw [← this, hsp]
    · have := hR' r
      by_cases hb : r = .rbx
      · subst hb; rw [hbx, Option.some.injEq, val_i64_inj] at this; exact this.symm
      by_cases hc : r = .r12
      · subst hc; rw [hr12, Option.some.injEq, val_i64_inj] at this; exact this.symm
      rw [hoth r h1 h2 h3 hb hc, Option.some.injEq, val_i64_inj] at this; exact this.symm
    · rw [hip, Option.some.injEq, val_i64_inj] at hw'''
      rw [← hw''']; exact hret

/-- **The x86 problem of `f`, solved by reduction to the Wasm problem.** -/
theorem x86_solution (b sp : Word) :
    XLProblemM (toyTab b) (toyWin sp) (ToyPre b sp) ToyPost :=
  xlproblemM_of_lproblemM (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False)
    (supported b sp) (wasm_solution b sp)

end Silmaril.Sim.X86.Toy
