module

public import Silmaril.Containers.Fixtures.Defs
public import Silmaril.Containers.Precondition.Thms

/-!
# Proofs: the fixtures under the small runtime model

Proofs for `Silmaril.Containers.Fixtures.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Fixtures

open Silmaril.Containers Silmaril.Containers.Fixtures

theorem load_image (p : Tiny) (e : List PortSpec) : small.load (image p e) = .ok p := rfl

theorem beh_image (p : Tiny) (e : List PortSpec) (b : Beh Ev) :
    small.beh (image p e) b ↔ Tiny.sem p b := by
  rw [Runtime.beh_ok (load_image p e)]
  exact ⟨fun ⟨_, h, he⟩ => he ▸ h, fun h => ⟨b, h, rfl⟩⟩

theorem always_nil {ok : Ev → Prop} {b : Beh Ev} (h : ∀ u, b.Prefix u → u = []) :
    Spec.always ok b := by
  intro u hu e he
  rw [h u hu] at he
  cases he

theorem prefix_done_nil {s : Stop} {u : List Ev} (h : (Beh.done [] s).Prefix u) : u = [] :=
  List.eq_nil_of_prefix_nil h

/-! ## No-op, crash, spin -/

theorem noop_wp : wp small (fun t c => t = [] ∧ c = 0) noop := by
  intro b hb
  replace hb := (beh_image _ _ b).1 hb
  cases hb
  exact ⟨trivial, rfl, rfl⟩

theorem noop_confined : pre small (Spec.always fun e => Profile.none e.cap = true) noop := by
  intro b hb
  replace hb := (beh_image _ _ b).1 hb
  cases hb
  exact always_nil fun _ => prefix_done_nil

theorem crash_wlp (post : List Ev → UInt8 → Prop) : wlp small post crash := by
  intro b hb
  replace hb := (beh_image _ _ b).1 hb
  cases hb
  exact ⟨trivial, trivial⟩

theorem crash_not_wp (post : List Ev → UInt8 → Prop) : ¬ wp small post crash :=
  fun h => (h _ ((beh_image _ _ _).2 rfl)).2

theorem spin_wlp (post : List Ev → UInt8 → Prop) : wlp small post spin := by
  intro b hb
  replace hb := (beh_image _ _ b).1 hb
  cases hb
  exact ⟨trivial, trivial⟩

theorem spin_not_wp (post : List Ev → UInt8 → Prop) : ¬ wp small post spin :=
  fun h => (h _ ((beh_image _ _ _).2 rfl)).2

theorem spin_traceRefines_noop : (small.beh spin).TraceRefines (small.beh noop) := by
  rintro u ⟨b, hb, hu⟩
  replace hb := (beh_image _ _ b).1 hb
  cases hb
  exact ⟨_, (beh_image _ _ _).2 rfl, List.eq_nil_of_prefix_nil hu ▸ List.nil_prefix⟩

theorem spin_not_refines_noop : ¬ (small.beh spin).Refines (small.beh noop) := by
  intro h
  have := (beh_image _ _ _).1 (h _ ((beh_image _ _ _).2 rfl))
  cases this

/-- **The weakest precondition of "exit 0 with no events", on contents**: exactly the images
whose entry point is the program `exit 0`. -/
theorem wp_exit0_iff (img : Flat Blob) :
    wp small (fun t c => t = [] ∧ c = 0) img ↔ small.load img = .ok (.exit 0) := by
  constructor
  · intro h
    cases hl : small.load img with
    | error r =>
      exact (h _ ((Runtime.beh_error hl _).2 rfl)).2.elim
    | ok p =>
      have hrun : ∀ b, Tiny.sem p b → Spec.totalCorrect (fun t c => t = [] ∧ c = 0) b :=
        fun b hb => (h b ((Runtime.beh_ok hl b).2 ⟨b, hb, rfl⟩)).2
      cases p with
      | exit c => have := (hrun _ rfl).2; subst this; rfl
      | crash s => exact (hrun _ rfl).elim
      | spin => exact (hrun _ rfl).elim
      | httpServe port resp => exact (hrun _ (HttpRun.waitAccept [])).elim
      | vsockCompute port f => exact (hrun _ VsockRun.waitAccept).elim
  · intro hl b hb
    obtain ⟨b₀, hs, rfl⟩ := (Runtime.beh_ok hl b).1 hb
    cases hs
    exact ⟨trivial, rfl, rfl⟩

/-! ## HTTP over TCP -/

/-- The events the HTTP fixture can produce. -/
inductive HttpEv (port : Silmaril.Net.Ip.Port) (resp : List UInt8) : Ev → Prop where
  | socket : HttpEv port resp (.socket (lsock .inet4))
  | bind : HttpEv port resp (.bind (lsock .inet4) (anyV4 port))
  | listen : HttpEv port resp (.listen (lsock .inet4))
  | accept : HttpEv port resp (.accept (lsock .inet4) (csock .inet4))
  | recv (req) : HttpEv port resp (.recv (csock .inet4) req)
  | send : HttpEv port resp (.send (csock .inet4) resp)
  | close : HttpEv port resp (.close (csock .inet4))

theorem mem_httpTrace {port resp reqs} {e : Ev} (he : e ∈ httpTrace port resp reqs) :
    HttpEv port resp e := by
  simp only [httpTrace, httpSetup, httpSession, List.mem_append, List.mem_cons,
    List.mem_flatten, List.mem_map, List.not_mem_nil, or_false] at he
  rcases he with (rfl | rfl | rfl) | ⟨_, ⟨req, -, rfl⟩, he⟩
  · exact .socket
  · exact .bind
  · exact .listen
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact .accept
    · exact .recv req
    · exact .send
    · exact .close

theorem httpRun_events {port resp} {b : Beh Ev} (hb : HttpRun port resp b) {u : List Ev}
    (hu : b.Prefix u) {e : Ev} (he : e ∈ u) : HttpEv port resp e := by
  cases hb with
  | waitAccept reqs => exact mem_httpTrace (hu.subset he)
  | waitRecv reqs =>
    rcases List.mem_append.1 (hu.subset he) with h | h
    · exact mem_httpTrace h
    · rw [List.mem_singleton.1 h]; exact .accept
  | forever f hf =>
    obtain ⟨reqs, hr⟩ := hf u.length
    have hu' : u = (List.range u.length).map f := hu
    rw [← hu'] at hr
    exact mem_httpTrace (hr.subset he)

theorem http_events {b : Beh Ev} (hb : small.beh http b) {u : List Ev} (hu : b.Prefix u)
    {e : Ev} (he : e ∈ u) : HttpEv httpPort okResponse e :=
  httpRun_events ((beh_image _ _ _).1 hb) hu he

theorem HttpEv.tcp {port resp} {e : Ev} (h : HttpEv port resp e) :
    e.cap = .sock .inet4 .stream := by
  cases h <;> rfl

theorem http_confined : pre small (Spec.always fun e => Profile.tcpOnly e.cap = true) http :=
  fun _ hb _ hu _ he => by show Profile.tcpOnly _ = true; rw [(http_events hb hu he).tcp]; rfl

theorem http_sends_only :
    pre small (Spec.always fun e => ∀ s bs, e = .send s bs → bs = okResponse) http := by
  intro _ hb _ hu e he s bs hs
  have h := http_events hb hu he
  subst hs
  cases h
  rfl

theorem http_binds_declared : pre small (Spec.safe (BindsDeclared http.config)) http := by
  intro _ hb u hu s a hs
  have h := http_events hb hu hs
  cases h
  exact ⟨⟨.tcp, httpPort⟩, List.mem_singleton_self _, by decide, rfl, .inl ⟨rfl, rfl⟩⟩

theorem http_not_vsock :
    ¬ pre small (Spec.always fun e => Profile.vsockOnly e.cap = true) http := by
  intro h
  have := h _ ((beh_image _ _ _).2 (HttpRun.waitAccept [])) [.socket (lsock .inet4)]
    (by simp [Beh.Prefix, httpTrace, httpSetup]) _ (List.mem_singleton_self _)
  cases this

/-- Under an environment that eventually supplies every awaited input, the HTTP fixture never
stops. -/
theorem http_never_stops : pre small (Spec.under Beh.notBlocked fun b => ¬ b.Stopped) http := by
  intro b hb hnb hs
  cases (beh_image _ _ _).1 hb with
  | waitAccept => exact hnb
  | waitRecv => exact hnb
  | forever => exact hs

/-- Under a runtime that enforces vsock-only, the HTTP fixture is stopped before its first
event. -/
theorem http_enforce_vsock (b : Beh Ev) :
    (small.enforce Profile.vsockOnly).beh http b ↔ b = .done [] (.killed .policy) := by
  rw [Runtime.beh_ok (R := small.enforce Profile.vsockOnly) (i := http)
    (p := .httpServe httpPort okResponse) rfl]
  constructor
  · rintro ⟨b₀, hs, b₁, rfl, he⟩
    have hrun : small.beh http b₀ := (beh_image _ _ _).2 hs
    rcases he with ⟨ha, -⟩ | ⟨hu, -⟩ | ⟨t, e, hp, hc, -, rfl⟩
    · have hp : b₀.Prefix [.socket (lsock .inet4)] := by
        cases hs with
        | waitAccept reqs => simp [Beh.Prefix, httpTrace, httpSetup]
        | waitRecv reqs => simp [Beh.Prefix, httpTrace, httpSetup]
        | forever f hf =>
          obtain ⟨reqs, hr⟩ := hf 1
          have h0 : f 0 = .socket (lsock .inet4) := by
            simpa [httpTrace, httpSetup] using hr
          simp [Beh.Prefix, h0]
      have := ha _ hp _ (List.mem_singleton_self _)
      cases this
    · -- the HTTP fixture has no run with undefined behaviour
      exact (hu (by cases hs <;> trivial)).elim
    · cases t with
      | nil => rfl
      | cons x t =>
        have hx := hc x (.head _)
        rw [(http_events hrun (Beh.prefix_of_prefix hp (List.prefix_append _ _))
          (.head _)).tcp] at hx
        cases hx
  · rintro rfl
    refine ⟨_, HttpRun.waitAccept [], _, rfl,
      .inr (.inr ⟨[], .socket (lsock .inet4), ?_, ?_, rfl, rfl⟩)⟩
    · simp [Beh.Prefix, httpTrace, httpSetup]
    · exact fun _ h => nomatch h

/-! ## A vsock compute service (the enclave side of a Nitro Enclave) -/

/-- The events the vsock fixture can produce. -/
inductive VsockEv (port : UInt32) (f : Fn) : Ev → Prop where
  | socket : VsockEv port f (.socket (lsock .vsock))
  | bind : VsockEv port f (.bind (lsock .vsock) (.vsock ⟨VsockAddr.cidAny, port⟩))
  | listen : VsockEv port f (.listen (lsock .vsock))
  | accept : VsockEv port f (.accept (lsock .vsock) (csock .vsock))
  | recv (x) : VsockEv port f (.recv (csock .vsock) x)
  | send (x) : VsockEv port f (.send (csock .vsock) (f.apply x))
  | close : VsockEv port f (.close (csock .vsock))

theorem vsockRun_events {port f} {b : Beh Ev} (hb : VsockRun port f b) {u : List Ev}
    (hu : b.Prefix u) {e : Ev} (he : e ∈ u) : VsockEv port f e := by
  cases hb with
  | waitAccept =>
    have hm := List.IsPrefix.subset hu he
    simp only [vsockSetup, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact .socket
    · exact .bind
    · exact .listen
  | waitRecv =>
    have hm := List.IsPrefix.subset hu he
    simp only [vsockSetup, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (rfl | rfl | rfl) | rfl
    · exact .socket
    · exact .bind
    · exact .listen
    · exact .accept
  | done x =>
    have hm := List.IsPrefix.subset hu he
    simp only [vsockTrace, vsockSetup, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl
    · exact .socket
    · exact .bind
    · exact .listen
    · exact .accept
    · exact .recv x
    · exact .send x
    · exact .close

theorem VsockEv.vsock {port f} {e : Ev} (h : VsockEv port f e) :
    Profile.vsockOnly e.cap = true := by
  cases h <;> rfl

theorem nitro_confined :
    pre small (Spec.always fun e => Profile.vsockOnly e.cap = true) nitro :=
  fun _ hb _ hu _ he => (vsockRun_events ((beh_image _ _ _).1 hb) hu he).vsock

theorem nitro_enforce_vsock (b : Beh Ev) :
    (small.enforce Profile.vsockOnly).beh nitro b ↔ small.beh nitro b :=
  Runtime.enforce_eq_of_confined nitro_confined b

/-- **Total correctness of the vsock service under a live environment**: it exits 0, and it
answered every request it received with the request reversed. -/
theorem nitro_total :
    pre small (Spec.under Beh.notBlocked (Spec.totalCorrect fun t c =>
      c = 0 ∧ ∀ x, Ev.recv (csock .vsock) x ∈ t → Ev.send (csock .vsock) x.reverse ∈ t))
      nitro := by
  intro b hb hnb
  cases (beh_image _ _ _).1 hb with
  | waitAccept => exact hnb.elim
  | waitRecv => exact hnb.elim
  | done x =>
    refine ⟨rfl, fun y hy => ?_⟩
    simp [vsockTrace, vsockSetup] at hy
    subst hy
    simp [vsockTrace, Fn.apply]

/-! ## The executable runner is sound -/

theorem run_sound (p : Tiny) (inputs : List (List UInt8)) : Tiny.sem p (Tiny.run p inputs) := by
  cases p with
  | exit c => rfl
  | crash s => rfl
  | spin => rfl
  | httpServe port resp => exact .waitAccept inputs
  | vsockCompute port f =>
    cases inputs with
    | nil => exact .waitAccept
    | cons x _ => exact .done x

/-! ## Environmental and internal nondeterminism -/

/-- Echo standard input once, then exit: nondeterministic only through its input. -/
def echoOnce : Model Ev := fun b => ∃ x, b = .done [.stdin x, .stdout x] (.exited 0)

/-- Print `0` or `1`, then exit: internally nondeterministic. -/
def coin : Model Ev := fun b => b = .done [.stdout [0]] (.exited 0) ∨ b = .done [.stdout [1]] (.exited 0)

theorem coin_not_det : ¬ Model.DetUpToInputs Ev.isInput coin := by
  rintro ⟨h, -⟩
  have := h _ _ [] (.stdout [0]) (.stdout [1]) (.inl rfl) (.inr rfl)
    (by simp [Beh.Prefix]) (by simp [Beh.Prefix]) (by simp)
  cases this.1

theorem echoOnce_det : Model.DetUpToInputs Ev.isInput echoOnce := by
  refine ⟨?_, ?_⟩
  · rintro b b' t e e' ⟨x, rfl⟩ ⟨y, rfl⟩ hp hp' hne
    -- both prefixes are prefixes of two-event traces starting with an input
    match t, hp, hp' with
    | [], hp, hp' =>
      simp [Beh.Prefix] at hp hp'
      subst hp; subst hp'
      exact ⟨rfl, rfl⟩
    | [a], hp, hp' =>
      simp [Beh.Prefix] at hp hp'
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨hxy, rfl⟩ := hp'
      cases hxy
      exact (hne rfl).elim
    | _ :: _ :: _, hp, _ =>
      have := hp.length_le
      simp at this
  · rintro t s s' ⟨x, hx⟩ ⟨y, hy⟩
    cases hx; cases hy; rfl

end Silmaril.Proofs.Containers.Fixtures

namespace Silmaril.Proofs.Containers.Fixtures

open Silmaril.Containers Silmaril.Containers.Fixtures

theorem noopCheck_iff (img : Flat Blob) : noopCheck img = true ↔ small.load img = .ok (.exit 0) := by
  unfold noopCheck
  cases small.load img with
  | error r => simp
  | ok p => cases p <;> simp

end Silmaril.Proofs.Containers.Fixtures
