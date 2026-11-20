module

public import Silmaril.Containers.Ports.Defs
public import Silmaril.Process.LPS.Sys.Socket
public import Silmaril.Process.LPS.MonadIff
public import Silmaril.Process.LPS.Probes.Kit
public import Silmaril.Process.LPS.Probes.KitMemory

/-!
# Proofs: the outcomes of LPS's socket calls a one-connection server makes

Proofs for `Silmaril.Containers.Ports.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Ports

open Silmaril.Containers.Ports
open Silmaril.Process.LPS

theorem socket_iff (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    socketSpec 2 1 0 i m o ↔
      (∃ e ∈ socketErrnos, o = errOut e m) ∨
      (fdLookup m.fds (allocFd m.fds) = none ∧
        o = .ok (mkEffect (allocFd m.fds) [] []) (m.withFds (fdInsert m.fds (allocFd m.fds) (.socket .fresh))) []) := by
  unfold socketSpec
  rw [Sys.bind_getModel_iff]
  simp (config := {decide := true}) only [↓reduceIte]
  cases o with
  | unmodeled => simp [Sys.bind, Sys.alt, errnoFrom, Sys.choose, errRet, retOnly, Sys.pure, Sys.setFds, Sys.modify, lowestFd, Bind.bind, errOut]
  | ok y m₂ evs =>
    simp [Sys.bind, Sys.alt, errnoFrom, Sys.choose, errRet, retOnly, Sys.pure, Sys.setFds, Sys.modify, lowestFd, Bind.bind, errOut]
    constructor
    · rintro (⟨x, ⟨hx, rfl, rfl⟩, rfl⟩ | ⟨⟨hf, rfl⟩, rfl, rfl⟩)
      · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
      · exact .inr ⟨hf, rfl, rfl, rfl⟩
    · rintro (⟨x, hx, rfl, rfl, rfl⟩ | ⟨hf, rfl, rfl, rfl⟩)
      · exact .inl ⟨x, ⟨hx, rfl, rfl⟩, rfl⟩
      · exact .inr ⟨⟨hf, rfl⟩, rfl, rfl⟩

theorem listen_iff (fd b : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (hfd : fdLookup m.fds fd = some (.socket .bound)) :
    listenSpec fd b i m o ↔
      o = .ok (mkEffect 0 [] []) (m.withFds (fdInsert m.fds fd (.socket .listening))) [] := by
  unfold listenSpec
  rw [Sys.bind_getModel_iff]
  simp only [hfd]
  cases o with
  | unmodeled => simp [Sys.bind, retOnly, Sys.pure, Sys.setFds, Sys.modify, Bind.bind]
  | ok y m₂ evs =>
    simp [Sys.bind, retOnly, Sys.pure, Sys.setFds, Sys.modify, Bind.bind]
    constructor
    · rintro ⟨⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem accept_iff (fd : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (hfd : fdLookup m.fds fd = some (.socket .listening)) (hex : connIxExhausted m.connIx = false) :
    accept4Spec fd 0 0 0 i m o ↔
      (∃ e ∈ acceptErrnos, o = errOut e m) ∨
      (fdLookup m.fds (allocFd m.fds) = none ∧
        o = .ok (mkEffect (allocFd m.fds) [] [])
          (m.withAccepted (fdInsert m.fds (allocFd m.fds)
            (.socket (.connected (nqPeer m.net) (connChannel m.connIx) (nqScript m.net))))) []) := by
  unfold accept4Spec
  rw [Sys.bind_getModel_iff]
  simp (config := {decide := true}) only [hfd, hex, ↓reduceIte]
  cases o with
  | unmodeled => simp (config := {decide := true}) [Sys.bind, Sys.alt, errnoFrom, Sys.choose, errRet, retOnly, Sys.pure, Sys.modify, lowestFd, Bind.bind, errOut]
  | ok y m₂ evs =>
    simp (config := {decide := true}) [Sys.bind, Sys.alt, errnoFrom, Sys.choose, errRet, retOnly, Sys.pure, Sys.modify, lowestFd, Bind.bind, errOut]
    constructor
    · rintro (⟨x, ⟨hx, rfl, rfl⟩, rfl⟩ | ⟨⟨hf, rfl⟩, rfl, rfl⟩)
      · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
      · exact .inr ⟨hf, rfl, rfl, rfl⟩
    · rintro (⟨x, hx, rfl, rfl, rfl⟩ | ⟨hf, rfl, rfl, rfl⟩)
      · exact .inl ⟨x, ⟨hx, rfl, rfl⟩, rfl⟩
      · exact .inr ⟨⟨hf, rfl⟩, rfl, rfl⟩

/-- `sendto(fd, buf, count, MSG_NOSIGNAL, NULL, 0)` on a connection whose stream has no pending
error, with a readable source: any non-empty prefix of the source is sent. -/
theorem sendto_goes_iff (fd buf count : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {bs : List Byte}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hs : sendState (.connected peer ch rx) = .goes ch)
    (hc : modeledRwCount count = true) (hz : wIs0 count = false)
    (ha : accessOkbX86 buf (uns count) = true)
    (hb : readableBytes i.mem buf count = bs) (hne : bs ≠ []) :
    sendtoSpecX86 fd buf count 0x4000 0 0 i m o ↔
      ∃ ds : List Byte, (1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ uns count ∧ ds = bs.take ds.length) ∧
        o = .ok ((mkEffect (lenWord ds) [] []).withCopyins [(buf, ds.length)]) m (ds.map (.writeEv ch)) := by
  unfold sendtoSpecX86 sendtoSpecWith
  have hf : sendFlagsModeled (0x4000 : Word) = true := by decide
  have h0 : wIs0 (0 : Word) = true := by decide
  simp only [hf, h0, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  simp only [accessOkZeroX86, ha, ↓reduceIte, hfd, sendOnSocket, hs, sendBytes, hz, hb]
  have hl : (bs.length == 0) = false := by cases bs <;> simp_all
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  cases o with
  | unmodeled => simp [Sys.bind, Sys.choose, Sys.emit, recordCopyins, retOnly, Sys.pure, Bind.bind]
  | ok y m₂ evs =>
    simp [Sys.bind, Sys.choose, Sys.emit, recordCopyins, retOnly, Sys.pure, Bind.bind]
    constructor
    · rintro ⟨x, hx, ⟨rfl, rfl⟩, rfl⟩; exact ⟨x, hx, rfl, rfl, rfl⟩
    · rintro ⟨x, hx, rfl, rfl, rfl⟩; exact ⟨x, hx, ⟨rfl, rfl⟩, rfl⟩

/-- The same call on a connection whose stream has a pending error `e`: the error is returned,
and the socket is left reset. -/
theorem sendto_err_iff (fd buf count : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {e : Int}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hs : sendState (.connected peer ch rx) = .err e peer ch)
    (hc : modeledRwCount count = true) (ha : accessOkbX86 buf (uns count) = true) :
    sendtoSpecX86 fd buf count 0x4000 0 0 i m o ↔
      o = .ok ((mkEffect (errnoRet e) [] []).withCopyins [])
        (m.withFds (fdInsert m.fds fd (.socket (.reset peer ch)))) [] := by
  unfold sendtoSpecX86 sendtoSpecWith
  have hf : sendFlagsModeled (0x4000 : Word) = true := by decide
  have h0 : wIs0 (0 : Word) = true := by decide
  simp only [hf, h0, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  simp only [accessOkZeroX86, ha, ↓reduceIte, hfd, sendOnSocket, hs]
  cases o with
  | unmodeled => simp [Sys.bind, Sys.setFds, Sys.modify, errRet, recordCopyins, retOnly, Sys.pure, Bind.bind]
  | ok y m₂ evs =>
    simp [Sys.bind, Sys.setFds, Sys.modify, errRet, recordCopyins, retOnly, Sys.pure, Bind.bind]
    constructor
    · rintro ⟨⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, rfl⟩

set_option maxRecDepth 100000 in
theorem lookup_sock (n : Nat) (h : (lookupArm (fsIoX86Arms ++ fsMetaX86Arms ++ fsCtlX86Arms ++
    fdEventsX86Arms ++ mmX86Arms ++ exitX86Arms ++ forkX86Arms ++ kernelSysX86Arms ++ signalX86Arms ++
    futexX86Arms) n).isNone = true) :
    lookupArm familyX86Arms n = lookupArm socketX86Arms n := by
  rw [familyX86Arms, NativeX86.All.lookupArm_append, Option.isNone_iff_eq_none.1 h, Option.none_or]

theorem dispatches_socket :
    Probes.Dispatches 41 (fun i => socketSpec (i.arg 0) (i.arg 1) (i.arg 2)) :=
  Probes.dispatches_slot ⟨198, 41, "socket"⟩ (by decide) ((lookup_sock 41 (by decide +kernel)).trans rfl) (by decide)

theorem dispatches_listen :
    Probes.Dispatches 50 (fun i => listenSpec (fd32 (i.arg 0)) (i.arg 1)) :=
  Probes.dispatches_slot ⟨201, 50, "listen"⟩ (by decide) ((lookup_sock 50 (by decide +kernel)).trans rfl) (by decide)

theorem dispatches_accept :
    Probes.Dispatches 43 (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) 0) :=
  Probes.dispatches_slot ⟨202, 43, "accept"⟩ (by decide) ((lookup_sock 43 (by decide +kernel)).trans rfl) (by decide)

theorem dispatches_sendto :
    Probes.Dispatches 44 (fun i => sendtoSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)) :=
  Probes.dispatches_slot ⟨206, 44, "sendto"⟩ (by decide) ((lookup_sock 44 (by decide +kernel)).trans rfl) (by decide)


section Read
open Silmaril.Process.LPS.Probes
theorem netTakeFrom_length_le (s : NetStream) : ∀ (start k : Nat), (s.takeFrom start k).length ≤ k
  | _, 0 => by simp [NetStream.takeFrom]
  | start, k + 1 => by
    unfold NetStream.takeFrom
    split
    · simp
    · simp only [List.length_cons]; have := netTakeFrom_length_le s (start + 1) k; omega

theorem read_fin_iff (fd buf : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    {peer : PeerAddr} {ch : Word} {rx : NetStream}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hi : rx.item 0 = .inr .fin) (ha : accessOkbX86 buf 1024 = true) :
    readSpecX86 fd buf 1024 i m o ↔ o = .ok (mkEffect 0 [] []) m [] := by
  unfold readSpecX86 readSpecWith
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  have hm : modeledRwRangeWith accessOkbX86 buf 1024 = true := by
    unfold modeledRwRangeWith; rw [show modeledRwCount 1024 = true by decide]; rfl
  have hz : wIs0 (1024 : Word) = false := by decide
  have hu : uns (1024 : Word) = 1024 := by decide
  simp only [hfd, hm, hz, hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte, accessOkZeroWith, hu, ha]
  cases o <;> simp [retOnly, Sys.pure]

theorem read_err_iff (fd buf : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {e : NetEnd} {err : Int}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hi : rx.item 0 = .inr e) (he : (e = .rst ∧ err = ECONNRESET) ∨ (e = .timedOut ∧ err = ETIMEDOUT))
    (ha : accessOkbX86 buf 1024 = true) :
    readSpecX86 fd buf 1024 i m o ↔
      o = .ok (mkEffect (errnoRet err) [] []) (m.withFds (fdInsert m.fds fd (.socket (.reset peer ch)))) [] := by
  unfold readSpecX86 readSpecWith
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  have hm : modeledRwRangeWith accessOkbX86 buf 1024 = true := by
    unfold modeledRwRangeWith; rw [show modeledRwCount 1024 = true by decide]; rfl
  have hz : wIs0 (1024 : Word) = false := by decide
  have hu : uns (1024 : Word) = 1024 := by decide
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [hfd, hm, hz, hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte, socketPendingErrorWith,
      accessOkZeroWith, hu, ha]
    cases o with
    | unmodeled => simp [errRet, retOnly, Sys.pure, Sys.bind, Sys.modify, Bind.bind]
    | ok => simp [errRet, retOnly, Sys.pure, Sys.bind, Sys.modify, Bind.bind]; tauto


theorem read_data_iff (fd buf : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {b : Byte}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hi : rx.item 0 = .inl b)
    (writable : ∀ k ≤ 1024, (readBytesAux i.wmem buf k).isSome = true) :
    readSpecX86 fd buf 1024 i m o ↔ ∃ bs, ReadOk rx bs ∧
      o = .ok (mkEffect (lenWord bs) [(buf, bs)] [])
        (m.withFds (fdInsert m.fds fd (.socket (.connected peer ch (rx.take bs.length).2))))
        (bs.map (.readEv ch)) := by
  have hm : modeledRwRangeWith accessOkbX86 buf 1024 = true := by
    unfold modeledRwRangeWith; rw [show modeledRwCount 1024 = true by decide]; rfl
  have hz : wIs0 (1024 : Word) = false := by decide
  have hclamp : rwCountClamp (1024 : Word) = 1024 := by decide
  have writableWord (l : List Byte) (bound : l.length ≤ 1024) :
      (readBytesMap i.wmem buf (lenWord l)).isSome = true := by
    unfold readBytesMap
    rw [lenWord_toNat l (by omega)]
    exact writable _ bound
  obtain ⟨first, firstOk⟩ := Option.isSome_iff_exists.mp (writable 1 (by omega))
  have firstMap : readBytesMap i.wmem buf 1#64 = some first := firstOk
  have takeBound : (rx.takeZ (1024 : Int)).1.length ≤ 1024 := by
    unfold NetStream.takeZ NetStream.take
    simp only [show (0 : Int) < 1024 by decide, ↓reduceIte]
    exact netTakeFrom_length_le rx 0 _
  obtain ⟨whole, wholeOk⟩ := Option.isSome_iff_exists.mp
    (writableWord (rx.takeZ (1024 : Int)).1 takeBound)
  unfold readSpecX86 readSpecWith
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  simp only [hfd, hm, hz, hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hclamp, wholeOk]
  have firstMap' : readBytesMap i.wmem buf 1 = some first := firstOk
  rw [firstMap']
  cases o with
  | ok effect model' evs =>
    simp [Sys.bind, Sys.choose, Sys.modify, Sys.emit, Sys.pure, bind, Bind.bind]
    constructor
    · rintro ⟨bs, ⟨h1, h2, h3, -⟩, ⟨rfl, rfl⟩, rfl⟩
      exact ⟨bs, ⟨h1, h2, h3⟩, rfl, rfl, rfl⟩
    · rintro ⟨bs, ⟨h1, h2, h3⟩, rfl, rfl, rfl⟩
      exact ⟨bs, ⟨h1, h2, h3, writableWord bs h2⟩, ⟨rfl, rfl⟩, rfl⟩
  | unmodeled => simp [Sys.bind, Sys.choose, Sys.modify, Sys.emit, Sys.pure, bind, Bind.bind]

end Read

end Silmaril.Proofs.Containers.Ports
