module

public import Silmaril.Containers.Mini.Defs
public import Silmaril.Containers.Machine.Thms

/-!
# Proofs: the minimal machine

Proofs for `Silmaril.Containers.Mini.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Mini

open Silmaril.Containers Silmaril.Containers.Mach Silmaril.Containers.Mini

theorem step_tau {s s' : List Instr} (h : mini.step s .tau s') : s' = s ∧ ∃ r, s = .spin :: r := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h
    exact ⟨h, rest, rfl⟩

theorem step_ev {s s' : List Instr} {e : Ev} (h : mini.step s (.ev e) s') : s = .emit e :: s' := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; rfl

theorem step_clone {s s' : List Instr} {r : CloneReq} (h : mini.step s (.clone r) s') :
    s = .clone r :: s' := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; rfl

theorem internal_seq {a : Act Ev} (h : Internal seqPolicy a) : a = .tau := by
  cases a with
  | tau => rfl
  | ev e => exact h.elim
  | clone r => exact absurd (show seqPolicy r = none from h) (by simp [seqPolicy])

theorem exec_inv {s s' : mini.State} {t : List Ev} (h : mini.Exec seqPolicy s t s') :
    (s : List Instr) = t.map .emit ++ s' := by
  induction h with
  | refl => rfl
  | internal ha hs _ ih => rw [internal_seq ha] at hs; exact (step_tau hs).1 ▸ ih
  | ev hs _ ih => rw [step_ev hs, ih]; rfl

theorem exec_emits (es : List Ev) (q : List Instr) :
    mini.Exec seqPolicy (es.map .emit ++ q) es q := by
  induction es with
  | nil => exact .refl _
  | cons e es ih => exact .ev (s' := es.map .emit ++ q) ⟨rfl, rfl⟩ ih

theorem result_emits (es : List Ev) (q : List Instr) :
    result (es.map .emit ++ q) = es.foldr cons (result q) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, List.cons_append, result, ih, List.foldr_cons]

theorem foldr_done (es t : List Ev) (s : Stop) :
    es.foldr cons (.done t s) = .done (es ++ t) s := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.foldr_cons, ih, cons, List.cons_append]

theorem foldr_spins (es t : List Ev) : es.foldr cons (.spins t) = .spins (es ++ t) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.foldr_cons, ih, cons, List.cons_append]

theorem splitEmits (p : List Instr) :
    ∃ (es : List Ev) (q : List Instr), p = es.map .emit ++ q ∧ ∀ e r, q ≠ .emit e :: r := by
  induction p with
  | nil => exact ⟨[], [], rfl, fun _ _ h => nomatch h⟩
  | cons i p ih =>
    by_cases hi : ∃ e, i = .emit e
    · obtain ⟨e, rfl⟩ := hi
      obtain ⟨es, q, rfl, hq⟩ := ih
      exact ⟨e :: es, q, rfl, hq⟩
    · exact ⟨[], i :: p, rfl, fun e r h => hi ⟨e, (List.cons.inj h).1⟩⟩

theorem final_result {s : List Instr} {st : Stop} (h : mini.final s st) :
    result s = .done [] st := by
  rcases s with _ | ⟨i, rest⟩
  · exact h.elim
  · cases i <;> simp at h <;> (subst h; rfl)

theorem stuck_result {s : List Instr} (h : mini.Stuck s) : result s = .done [] (.undefined .stuck) := by
  rcases s with _ | ⟨i, rest⟩
  · rfl
  · cases i with
    | emit e => exact (h.1 (.ev e) rest ⟨rfl, rfl⟩).elim
    | clone r => exact (h.1 (.clone r) rest ⟨rfl, rfl⟩).elim
    | exit c => exact (h.2 (.exited c) rfl).elim
    | crash g => exact (h.2 (.signaled g) rfl).elim
    | spin => exact (h.1 .tau _ ⟨rfl, rfl⟩).elim

theorem runs_iff {p : List Instr} (hp : OutputOnly p) (b : Beh Ev) :
    mini.Run seqPolicy p b ↔ b = result p := by
  constructor
  · intro h
    cases h with
    | @final s s' t st hs hx hf =>
      subst hs
      rw [exec_inv hx, result_emits, final_result hf, foldr_done, List.append_nil]
    | @clone s s' s'' t r u hs hx hc hu =>
      subst hs
      cases hu
      rw [exec_inv hx, result_emits, step_clone hc,
        show result (Instr.clone r :: s'') = .done [] (.undefined r.ub) from rfl, foldr_done,
        List.append_nil]
    | @stuck s s' t hs hx hst =>
      subst hs
      rw [exec_inv hx, result_emits, stuck_result hst, foldr_done, List.append_nil]
    | @blocked s s' t hs hx hw =>
      subst hs
      obtain ⟨e, s'', hin, he⟩ := hw.2.1
      have hmem : Instr.emit e ∈ s := by
        rw [exec_inv hx, step_ev he]; simp
      have hin' : e.isInput = true := hin
      rw [hp e hmem] at hin'; cases hin'
    | @spins s s' t hs hx hd =>
      subst hs
      obtain ⟨f, hf0, hf⟩ := hd
      obtain ⟨a, ha, h0⟩ := hf 0
      rw [internal_seq ha] at h0
      obtain ⟨-, r, hr⟩ := step_tau h0
      rw [hf0] at hr
      rw [exec_inv hx, result_emits, hr, show result (Instr.spin :: r) = .spins [] from rfl,
        foldr_spins, List.append_nil]
    | reactive f hf =>
      obtain ⟨s, s', hs, hx⟩ := hf (p.length + 1)
      subst hs
      have := congrArg List.length (exec_inv hx)
      simp at this
      omega
    | noInit h => exact (h p rfl).elim
  · rintro rfl
    obtain ⟨es, q, rfl, hq⟩ := splitEmits p
    rw [result_emits]
    rcases q with _ | ⟨i, rest⟩
    · rw [show result [] = .done [] (.undefined .stuck) from rfl, foldr_done, List.append_nil es]
      exact .stuck (s' := ([] : List Instr)) rfl (exec_emits es [])
        ⟨fun _ _ h => h, fun _ h => h⟩
    · cases i with
      | emit e => exact (hq e rest rfl).elim
      | clone r =>
        rw [show result (.clone r :: rest) = .done [] (.undefined r.ub) from rfl, foldr_done,
          List.append_nil]
        exact .clone rfl (exec_emits es _) (s'' := rest) ⟨rfl, rfl⟩ rfl
      | exit c =>
        rw [show result (.exit c :: rest) = .done [] (.exited c) from rfl, foldr_done,
          List.append_nil]
        exact .final rfl (exec_emits es _) rfl
      | crash g =>
        rw [show result (.crash g :: rest) = .done [] (.signaled g) from rfl, foldr_done,
          List.append_nil]
        exact .final rfl (exec_emits es _) rfl
      | spin =>
        rw [show result (.spin :: rest) = .spins [] from rfl, foldr_spins, List.append_nil]
        exact .spins rfl (exec_emits es _)
          ⟨fun _ => .spin :: rest, rfl, fun _ => ⟨.tau, trivial, rfl, rfl⟩⟩

theorem beh_mimage {p : List Instr} (hp : OutputOnly p) (b : Beh Ev) :
    machRT.beh (mimage p) b ↔ b = result p := by
  rw [Runtime.beh_ok (R := machRT) (i := mimage p) (p := p) rfl]
  exact ⟨fun ⟨_, h, he⟩ => he ▸ (runs_iff hp _).1 h, fun h => ⟨b, (runs_iff hp _).2 h, rfl⟩⟩

theorem wlp_iff {p : List Instr} (hp : OutputOnly p) (post : List Ev → UInt8 → Prop) :
    wlp machRT post (mimage p) ↔ Spec.noUB (result p) ∧ Spec.partialCorrect post (result p) :=
  ⟨fun h => h _ ((beh_mimage hp _).2 rfl), fun h b hb => ((beh_mimage hp b).1 hb) ▸ h⟩

theorem wp_iff {p : List Instr} (hp : OutputOnly p) (post : List Ev → UInt8 → Prop) :
    wp machRT post (mimage p) ↔ Spec.noUB (result p) ∧ Spec.totalCorrect post (result p) :=
  ⟨fun h => h _ ((beh_mimage hp _).2 rfl), fun h b hb => ((beh_mimage hp b).1 hb) ▸ h⟩

theorem pre_iff {p : List Instr} (hp : OutputOnly p) (φ : Spec Ev) :
    pre machRT φ (mimage p) ↔ φ (result p) :=
  ⟨fun h => h _ ((beh_mimage hp _).2 rfl), fun h b hb => ((beh_mimage hp b).1 hb) ▸ h⟩

theorem tcpThenThread_out : OutputOnly tcpThenThread := by
  intro e he; simp [tcpThenThread] at he; subst he; rfl

theorem tcpThenThread_not_wlp (post : List Ev → UInt8 → Prop) :
    ¬ wlp machRT post (mimage tcpThenThread) :=
  not_wlp_of_undefined ((beh_mimage tcpThenThread_out _).2 rfl) post

/-- Under vsock-only enforcement the only run is a policy kill before any event: the thread
creation is pre-empted, not hidden. -/
theorem tcpThenThread_enforce (b : Beh Ev) (hb : (machRT.enforce Profile.vsockOnly).beh
    (mimage tcpThenThread) b) : b = .done [] (.killed .policy) := by
  obtain ⟨b₀, hs, b₁, rfl, he⟩ := (Runtime.beh_ok (R := machRT.enforce Profile.vsockOnly)
    (i := mimage tcpThenThread) (p := tcpThenThread) rfl b).1 hb
  have h₀ : b₀ = result tcpThenThread := (runs_iff tcpThenThread_out b₀).1 hs
  subst h₀
  rcases he with ⟨ha, -⟩ | ⟨t, e, hp, -, -, rfl⟩
  · have := ha [.socket (Fixtures.lsock .inet4)] (List.prefix_refl _) _ (List.mem_singleton_self _)
    cases this
  · have hp' : t ++ [e] <+: [Ev.socket (Fixtures.lsock .inet4)] := hp
    have hl := hp'.length_le
    have ht : t = [] := by
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [ht]

theorem tcpThenThread_wlp_enforce (post : List Ev → UInt8 → Prop) :
    wlp (machRT.enforce Profile.vsockOnly) post (mimage tcpThenThread) := by
  intro b hb
  rw [tcpThenThread_enforce b hb]
  exact ⟨trivial, trivial⟩

/-- Handing task creation to a machine that does not implement it: under `machinePolicy` the
thread request of `threadSpawn` is a step of `mini` that creates nothing, and the program exits
0. -/
theorem noTasks_threadSpawn_exits :
    (machR.withMachine mini machinePolicy).toRuntime.beh (mimage threadSpawn)
      (.done [] (.exited 0)) :=
  (Runtime.beh_ok (R := (machR.withMachine mini machinePolicy).toRuntime)
    (i := mimage threadSpawn) (p := threadSpawn) rfl _).2
    ⟨_, .final rfl (.internal (a := .clone (.clone 0x3d0f00)) rfl ⟨rfl, rfl⟩ (.refl _)) rfl, rfl⟩

theorem outputOnlyB_iff (p : List Instr) : outputOnlyB p = true ↔ OutputOnly p := by
  unfold outputOnlyB OutputOnly
  rw [List.all_eq_true]
  constructor
  · intro h e he
    have := h _ he
    simpa using this
  · intro h i hi
    cases i with
    | emit e => simp [h e hi]
    | _ => rfl

theorem noUBB_iff (b : Beh Ev) : noUBB b = true ↔ Spec.noUB b := by
  rcases b with ⟨t, s⟩ | _ | _ | _ <;> try exact ⟨fun _ => trivial, fun _ => rfl⟩
  cases s <;> simp [noUBB, Spec.noUB, Stop.isUB]

theorem beh_of_load {img : Flat (List Instr)} {p : List Instr} (hl : machRT.load img = .ok p)
    (hp : OutputOnly p) (b : Beh Ev) : machRT.beh img b ↔ b = result p := by
  rw [Runtime.beh_ok hl]
  exact ⟨fun ⟨_, h, he⟩ => he ▸ (runs_iff hp _).1 h, fun h => ⟨b, (runs_iff hp _).2 h, rfl⟩⟩

theorem noUBCheck_sound (img : Flat (List Instr)) (h : noUBCheck img = true) :
    wlp machRT (fun _ _ => True) img := by
  unfold noUBCheck at h
  cases hl : machRT.load img with
  | error r => rw [hl] at h; cases h
  | ok p =>
    rw [hl] at h
    obtain ⟨ho, hu⟩ := Bool.and_eq_true_iff.1 h
    have hp := (outputOnlyB_iff p).1 ho
    intro b hb
    rw [(beh_of_load hl hp b).1 hb]
    exact ⟨(noUBB_iff _).1 hu, by rcases result p with ⟨t, ⟨⟩⟩ | _ | _ | _ <;> trivial⟩

end Silmaril.Proofs.Containers.Mini
