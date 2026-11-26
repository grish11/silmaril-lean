# Abstract Linux I/O in interaction trees

The slice starts with a shared table of already-open descriptors and programs in the existing weak
`Silmaril.Elgot.ITree.Tree`. Import `Silmaril.Process.AbstractIO.Thms` for the syscall signature,
store, transitions, and laws. Import `Silmaril.Process.AbstractIO.API.Defs` for the file and network
interpreters, and `Silmaril.Process.AbstractIO.Bridge.Defs` for the partial ABI-facing data maps.
`Silmaril.Process.ITreeTrace.Thms` is independent of the I/O profile and works with any
`TypedSyscall.Signature` and `TypedSyscall.Kernel`. [Typed user/kernel boundary](typed-syscall.md)

## Calls and shared state

- A file descriptor names an open file description, which in turn names the backing file. Descriptors
  that alias the same description share its offset and access mode. Independent opens can have
  distinct descriptions of the same backing file. Successful `read` and `write` advance the shared
  offset by the returned byte count, including a zero advance at EOF. `pread` leaves the whole store
  unchanged and `pwrite` leaves every description unchanged. Positive writes overwrite a prefix of
  the supplied bytes and zero-fill any gap before the start of that prefix. [read(2)](https://man7.org/linux/man-pages/man2/read.2.html) · [write(2)](https://man7.org/linux/man-pages/man2/write.2.html) · [pread(2)](https://man7.org/linux/man-pages/man2/pread.2.html) · [open(2)](https://man7.org/linux/man-pages/man2/open.2.html)
- A connected stream has an initially supplied receive queue and peer FIN indication. Positive receives
  consume a prefix of the queue. Once it is empty, a positive receive reports EOF after peer FIN and
  would-block otherwise. A zero-size receive has its own result. Sends append accepted bytes to a
  local transmit log and consume the available send capacity. An empty send reports zero bytes and
  a positive send with no capacity reports would-block. Ordinary `read` and `write` also work on these
  streams, with `EAGAIN` for would-block and a zero-length read result for either EOF or a zero-size
  request. The model has no packets, message boundaries, peer delivery, arrival transitions or send
  queue draining. [send(2)](https://man7.org/linux/man-pages/man2/send.2.html) · [recv(2)](https://man7.org/linux/man-pages/man2/recv.2.html) · [tcp(7)](https://man7.org/linux/man-pages/man7/tcp.7.html)
- Each call chooses a positive byte cap up to `Syscall.maxTransfer`. A completed call uses the largest
  prefix allowed by the cap, request and available data or send capacity. `step` computes one such
  choice and `kernel` relates all choices, with no probability or OS progress claim. The request and
  its typed reply form the observation. Reported descriptor errors are `EBADF` for absent descriptors
  and denied file access, `ESPIPE` for positioned calls on streams, and `ENOTSOCK` for explicit socket
  calls on files. A dangling table entry is treated as a bad descriptor. All supported errors leave
  the store unchanged.

The model uses natural-number descriptors, lengths and offsets. Its scope excludes memory accesses,
signed offset checks and overflow, capacity errors from filesystems, durability, signals, reset,
timeouts, and all flags other than the choice of a nonblocking socket profile. It has no descriptor,
process or socket lifecycle calls. Initial descriptors can already alias. Append is excluded: Linux
`pwrite` on an `O_APPEND` descriptor appends despite its explicit offset. The model takes each
completed call as one atomic transition, with interleavings at those call boundaries. [pread(2)](https://man7.org/linux/man-pages/man2/pread.2.html)

## Finite runs and API interpretation

`Flatten` drives one selected thread at a time, with the kernel relation supplying all legal
completions for its current request and shared store. Its label projection sees the selected thread
and the kernel label on each completion, including process-wide kernel exit when the kernel has an
exit rule. `Interleaving` keeps both fields. `Sequential` selects the only thread once for each unit
of fuel and keeps the kernel labels. `sequential_iff_singleton` proves equality of the realized
results after erasing thread tags, preserving the final store and endpoint in both directions.
`Flatten.relabel_iff` gives the more general projection law.

A pool has a fixed set of thread identifiers and a common return type. The runner reports successful
return when every thread is at a tree return and retains all of those values. A schedule slot
selecting an already returned thread is skipped while another thread remains live. An empty schedule
in a live pool reports exhaustion. A selected silent divergence or request with no kernel completion
stops the finite observation at that thread. A blocked observation is specific to the chosen thread
and store. A different schedule may select another thread. The abstract nonblocking I/O kernel
always completes, including when its reply is would-block. No fairness or infinite trace semantics is
assumed. `Allows` uses the existing `ITree.HasTrace` predicate and checks pending as well as completed
requests on every finite typed reply path. `pread_allows` checks the positioned-read policy.
`positioned_reads_store` lifts the per-call frame law to every finite run of a pool satisfying that
policy. `recv_eof` gives the stream EOF conditions.

`fileAPI` and `networkAPI` use `ITree.Interpret.foldHom`. Their maps preserve return, bind and
complete iteration and expand high-level events according to their handlers. A file copy at explicit
positions uses at most a `pread` and a `pwrite`; it returns the actual written count and skips the
write on empty input. Those two calls can interleave with other threads. The network send operation
returns the unsent suffix after a short acceptance. The receive operation returns a byte chunk,
EOF, a zero-size result, or would-block.

## Exact lowering and satisfaction

Import `Silmaril.Process.AbstractIO.Exact.Thms` to use `ITreeTrace.Exact.lowering` with a
`TypedSyscall.Signature.Hom`. Each source event lowers to one target request, and the target's
typed reply passes through the homomorphism's response function before the source continuation
resumes. The abstract Linux kernel retains all transfer choices and emits exactly one
`AbstractIO.Observation` per reply, carrying the actual request and its dependent reply.
The profile uses a unit environment and takes the initial `Store` from the caller. The same
store and concrete trace labels are used on both sides of institution satisfaction.

`copySentence` takes an initial-store predicate and an observation predicate. Its test is
`positionedCopy`, an explicit tree of positioned reads and writes. The theorem
`lower_positionedCopy` identifies the lowered tree with the existing `fileAPI` copy handler,
including the empty-read and error returns and the write on nonempty input.
`copy_satisfies_iff` applies exact satisfaction to that handler and the reduct of the abstract
Linux kernel. The copy is a program of up to two single-exchange events. For the nonblocking
network API, `lower_network_call` checks each existing handler against its single-exchange
lowering. A send projects a byte count to the unsent suffix and preserves the would-block and
error cases. A receive passes its typed reply through unchanged.

`ITreeTrace.Exact.returned_iff_sequential` compares the completed-return fragment with
`ITreeTrace.Sequential` (singleton `Flatten`). It preserves labels, return value and final
store in both directions. The finite runner needs fuel at least the log length, because each
completed call emits one label and inspecting a return uses no slot. Both sides use weak trees,
where `tau` is the identity. Exact silent divergence self-loops without labels; the finite
runner has separate silent and fuel-exhausted endpoints. The correspondence is restricted to completed
sequential returns. The lowering covers the single-exchange signature maps and the
explicit copy program above.

At the generic adapter boundary, a typed exit becomes an exact stop carrying status, final store
and one label. A visible request with no completion is blocked. In the abstract Linux profile,
every modeled request replies, and `finish_iff` shows that only a tree return can finish a run.
A would-block response or descriptor error is a completed typed reply. Unsupported syscalls
outside the request signature and ABI memory faults are outside this profile.

## Boundary with existing process models

- `ofByteStreamRequest` reads the request type of `TypedSyscall.Linux.signature`. It erases a read
  destination and takes an explicit copy-in function for writes, requiring the full source length.
  `byteStreamResult` recovers the count or errno for these operations. The bridge leaves buffer
  validation, copying read bytes out, and exit semantics to the caller. `Syscall.Step` models private
  streams and user memory, while this regular-file model uses shared descriptions and writable file
  contents. The maps establish data correspondence only. [Byte-stream syscall contract](../../Silmaril/Process/Syscall.lean)
- `ofLpsFile` projects the path, offset and access modes of LPS `.file`, `.fileW` and `.fileRW`.
  The caller assigns file identities by path, provides backing bytes, and determines descriptor
  aliasing. LPS's `readSpec`/`writeSpec` and `pread64Spec`/`pwrite64Spec` include ABI, memory and error
  cases beyond this profile. The LPS `dup` model declines entries whose per-descriptor offsets would
  be split by copying. LPS models connected `sendto` under `MSG_NOSIGNAL` and uses other receive paths
  such as regular `read`; its `recvfrom` arm declines connected reads. This slice supplies no
  simulation of an LPS syscall or ISA step. [LPS regular I/O](../../Silmaril/Process/LPS/Sys/ReadWrite.lean) · [Positioned I/O](../../Silmaril/Process/LPS/Sys/FsIo/ReadWrite.lean) · [LPS sockets](../../Silmaril/Process/LPS/Sys/Socket.lean)
- `Mt` also has a single-thread embedding and a shared base syscall layer. Its scheduler, CPU steps,
  memory models, thread creation and futex waits remain separate from the finite scheduler here.
  `Tcp.Service` models transport delivery with separate sender and receiver histories. This profile
  uses local socket queues, where accepted output alone gives no peer delivery guarantee. [Multithreaded process model](../../Silmaril/Process/Mt/Defs.lean) · [TCP service](../../Silmaril/Net/Tcp/Service/Defs.lean)

## Checks

`lake build --wfail +Silmaril.Proofs.Process.AbstractIO.Regression` checks a two-thread
interleaving over aliased descriptors, independent opens, short and positioned writes, stream
replies, the interpreted file and network operations, finite endpoints, and the boundary maps.
The `Silmaril` target includes the regression through its Process proof glob.
[Examples](../../Silmaril/Proofs/Process/AbstractIO/Regression.lean)

`lake build --wfail +Silmaril.Proofs.Process.AbstractIO.Exact.Regression` checks satisfaction
for the existing positioned copy handler with a fixed initial store and all transfer choices.
The regression checks completed traces against the finite runner, including a send that replies
would-block. It also evaluates the positioned and ordinary writes. The ordinary write copies
the same byte to the same location and is rejected for advancing the open description.
[Exact I/O regressions](../../Silmaril/Proofs/Process/AbstractIO/Exact/Regression.lean)
