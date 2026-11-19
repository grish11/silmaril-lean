# Nested caller/helper observation scope

The hidden private bytes and allocator/excluded-action bookkeeping are an explicit observation-adequacy gap: context-unobservability has not been proved. This abstraction is local to this nested-call problem, not full-memory or arbitrary-continuation equivalence. Original private parameter objects0/1 remain checked; caller root2, nodes3..n+2 and unrelated object n+3 retain complete allocation metadata, lifetime, bytes, pointer provenance and permissions. Actual fresh helper parameter/automatic allocations must be dead. The return projection accepts only null or the exact base/provenance of an original caller object; private/dangling-private returns are rejected. Other complete-record contexts are unchanged.

The initial private parameter objects are caller `array` (allocation0 at4096,
8-byte pointer) and caller `index` (allocation1 at4104,4-byte signed int); their
original records and bytes are preserved too. For a nonnegative caller index,
actual `get_array_item` receives fresh private parameter objects `array` and
`index` (the converted64-bit `size_t`), and allocates its actual automatic
`current_child` pointer. These objects come from the source-backed Core call and
local-declaration rules; their concrete IDs/addresses are not fabricated as
caller objects or replaced with contracts. Every fresh argument/local allocation
from the initial nextId through the final nextId must be dead. The negative-index
caller branch returns before calling the helper. Fresh-object allocation and
excluded-action counters remain hidden by this context's declared projection;
that abstraction is an unproved adequacy gap, not arbitrary-continuation safety.
