#!/usr/bin/env python3
"""Differential test of the handwritten forms of Str9Fs / Str9FsX / Str9G against the host CPU.

Oracle: this processor, executing each instruction natively (assembled by GNU as from AT&T
text, so the bytes are the assembler's encoding) between a prologue that loads all general
registers except rsp, the six status flags and the sixteen XMM registers from a state record,
and an epilogue that stores them back. Memory operands address a page-aligned buffer; FS-relative
operands address it through the real FS base (`arch_prctl(ARCH_GET_FS)`), the base register being
set so that `fsBase + base + index*scale + disp` lands in the buffer.

The Lean side (`Check.lean`) builds the same initial state (`Str9G.GState`: registers, flags,
XMM file, the buffer as a read-write region, the instruction bytes at `rip` in an executable
region, `fsBase`, `cetOff = true`, `tsc` = the counter value the native run returned), runs
`Str9G.step` until `rip` leaves the instruction (at most 64 steps: `rep stos` takes one element
per step), and compares registers, defined flags, XMM registers and the buffer.

Same pattern as silmaril-lean's `scripts/x86-features/x87_harness.py` (prologue, `.byte`/asm
form, epilogue, one function per case).

Usage: difftest.py [--seed N] [--per K] [--out DIR]    then  lake env lean tools/x86-difftest/Check.lean
"""
import argparse, os, random, re, subprocess, tempfile

ap = argparse.ArgumentParser()
ap.add_argument("--seed", type=int, default=1)
ap.add_argument("--per", type=int, default=40, help="cases per template")
ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out"))
args = ap.parse_args()
R = random.Random(args.seed)

R64 = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
R32 = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"]
GP = [i for i in range(16) if i != 4]   # never rsp

def rnd64():
    k = R.random()
    if k < 0.2: return R.choice([0, 1, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFF, 0x80000000])
    if k < 0.5: return R.getrandbits(32)
    return R.getrandbits(64)

def mem_operand(fs, align16=False):
    """An operand text, and the patch: (base reg, index reg, scale, disp, target offset, fs)."""
    b = R.choice(GP)
    t = R.randrange(0, 192) if not align16 else 16 * R.randrange(0, 12)
    shape = R.choice(["b", "db", "dbi"])
    disp = 0; i = -1; s = 1
    if shape in ("db", "dbi"): disp = R.choice([R.randrange(-128, 128), R.randrange(-100000, 100000)])
    if shape == "dbi":
        i = R.choice([r for r in GP if r != b]); s = R.choice([1, 2, 4, 8])
    txt = ("%fs:" if fs else "") + (str(disp) if disp else "") + "(%" + R64[b] + (",%" + R64[i] + "," + str(s) if i >= 0 else "") + ")"
    return txt, (b, i, s, disp, t, 1 if fs else 0)

def reg(n32=False, avoid=()):
    r = R.choice([g for g in GP if g not in avoid]); return ("%" + (R32 if n32 else R64)[r]), r

ALU = ["add", "or", "and", "sub", "xor", "cmp"]
def templates():
    T = []
    # --- Str9Fs: FS-relative forms ---
    def fs(f): T.append(("fs", f))
    fs(lambda: (lambda m, r: (f"mov {r[0]}, {m[0]}", m[1]))(mem_operand(True), reg(True)))
    fs(lambda: (lambda m, r: (f"mov {r[0]}, {m[0]}", m[1]))(mem_operand(True), reg(False)))
    fs(lambda: (lambda m, r: (f"mov {m[0]}, {r[0]}", m[1]))(mem_operand(True), reg(True)))
    fs(lambda: (lambda m, r: (f"mov {m[0]}, {r[0]}", m[1]))(mem_operand(True), reg(False)))
    fs(lambda: (lambda m, r: (f"movslq {m[0]}, {r[0]}", m[1]))(mem_operand(True), reg(False)))
    fs(lambda: (lambda m: (f"movl ${R.getrandbits(32)}, {m[0]}", m[1]))(mem_operand(True)))
    fs(lambda: (lambda m: (f"movq ${R.randrange(-2**31, 2**31)}, {m[0]}", m[1]))(mem_operand(True)))
    fs(lambda: (lambda m: (f"testl ${R.getrandbits(32)}, {m[0]}", m[1]))(mem_operand(True)))
    fs(lambda: (lambda m: (f"testq ${R.randrange(-2**31, 2**31)}, {m[0]}", m[1]))(mem_operand(True)))
    fs(lambda: (lambda m: (f"cmpb ${R.getrandbits(8)}, {m[0]}", m[1]))(mem_operand(True)))
    fs(lambda: (lambda m, r: (f"test {r[0]}, {m[0]}", m[1]))(mem_operand(True), reg(R.random() < 0.5)))
    for op in ALU:
        fs(lambda op=op: (lambda m: (f"{op}l ${R.getrandbits(32)}, {m[0]}", m[1]))(mem_operand(True)))
        fs(lambda op=op: (lambda m: (f"{op}q ${R.randrange(-128, 128)}, {m[0]}", m[1]))(mem_operand(True)))
        fs(lambda op=op: (lambda m, r: (f"{op} {r[0]}, {m[0]}", m[1]))(mem_operand(True), reg(R.random() < 0.5)))
        fs(lambda op=op: (lambda m, r: (f"{op} {m[0]}, {r[0]}", m[1]))(mem_operand(True), reg(R.random() < 0.5)))
    for op in ["incl", "decl", "incq", "decq"]:
        fs(lambda op=op: (lambda m: (f"{op} {m[0]}", m[1]))(mem_operand(True)))
    # --- Atomic9 forms through the Str9Fs chain ---
    def at(f): T.append(("atomic", f))
    at(lambda: (lambda m, r: (f"lock cmpxchg {r[0]}, {m[0]}", m[1]))(mem_operand(False), reg(R.random() < 0.5)))
    T.append(("cmpxchg-eq", lambda: (lambda m, r: (f"lock cmpxchg {r[0]}, {m[0]}", m[1]))(mem_operand(False), reg(R.random() < 0.5, avoid=(0,)))))
    at(lambda: (lambda m, r: (f"lock xadd {r[0]}, {m[0]}", m[1]))(mem_operand(False), reg(R.random() < 0.5)))
    at(lambda: (lambda m, r: (f"xchg {r[0]}, {m[0]}", m[1]))(mem_operand(False), reg(R.random() < 0.5)))
    at(lambda: (lambda m: (f"lock addl ${R.getrandbits(32)}, {m[0]}", m[1]))(mem_operand(False)))
    at(lambda: (lambda m: (f"lock orq ${R.randrange(-128, 128)}, {m[0]}", m[1]))(mem_operand(False)))
    at(lambda: (lambda m: (f"lock decl {m[0]}", m[1]))(mem_operand(False)))
    # --- Str9FsX: rep stosd ---
    T.append(("stosd", lambda: ("rep stosl", (7, -1, 1, 0, 4 * R.randrange(0, 32), 0))))
    # --- Str9G: SSE2 integer forms, rdtsc, CET hints ---
    def x(): return R.randrange(16)
    def sse(f): T.append(("sse2", f))
    for mn in ["pcmpeqb", "pminub", "psubb", "por", "pand", "punpcklbw", "punpcklwd"]:
        sse(lambda mn=mn: (f"{mn} %xmm{x()}, %xmm{x()}", None))
        sse(lambda mn=mn: (lambda m: (f"{mn} {m[0]}, %xmm{x()}", m[1]))(mem_operand(False, True)))
    sse(lambda: (f"pshufd ${R.getrandbits(8)}, %xmm{x()}, %xmm{x()}", None))
    sse(lambda: (lambda m: (f"pshufd ${R.getrandbits(8)}, {m[0]}, %xmm{x()}", m[1]))(mem_operand(False, True)))
    sse(lambda: (lambda r: (f"pmovmskb %xmm{x()}, {r[0]}", None))(reg(True)))
    sse(lambda: (f"psrldq ${R.randrange(0, 20)}, %xmm{x()}", None))
    sse(lambda: (f"pslldq ${R.randrange(0, 20)}, %xmm{x()}", None))
    for mn in ["movhps", "movhpd", "movlps", "movlpd", "movss", "movsd"]:
        sse(lambda mn=mn: (lambda m: (f"{mn} {m[0]}, %xmm{x()}", m[1]))(mem_operand(False)))
    for mn in ["movss", "movsd"]:
        sse(lambda mn=mn: (f"{mn} %xmm{x()}, %xmm{x()}", None))
    T.append(("rdtsc", lambda: ("rdtsc", None)))
    T.append(("cet", lambda: (lambda r: (f"rdsspq {r[0]}", None))(reg(False))))
    T.append(("cet", lambda: (lambda r: (f"incsspq {r[0]}", None))(reg(False))))
    return T

HARNESS_C = r"""
#include <signal.h>
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <asm/prctl.h>
#include <sys/syscall.h>
#include <unistd.h>
struct st { uint64_t r[16]; uint64_t fl; uint8_t x[256]; };
typedef void (*fn)(struct st *in, struct st *out);
extern fn table[];
static uint8_t buf[4096] __attribute__((aligned(4096)));
static sigjmp_buf jb;
static void onsig(int s) { (void)s; siglongjmp(jb, 1); }
static void hex(const char *s, uint8_t *o, int n) { for (int i = 0; i < n; i++) { unsigned v; sscanf(s + 2 * i, "%2x", &v); o[i] = v; } }
static void phex(const uint8_t *p, int n) { for (int i = 0; i < n; i++) printf("%02x", p[i]); }
int main(void) {
  unsigned long fsb; syscall(SYS_arch_prctl, ARCH_GET_FS, &fsb);
  struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_handler = onsig; sa.sa_flags = SA_NODEFER;
  sigaction(SIGSEGV, &sa, 0); sigaction(SIGBUS, &sa, 0); sigaction(SIGILL, &sa, 0); sigaction(SIGFPE, &sa, 0);
  static char line[1 << 16], sh[2048], sm[2048];
  static struct st in, out;
  int idx, b, i, s, kind; long disp, t;
  while (fgets(line, sizeof line, stdin)) {
    char *p = line; int n;
    if (sscanf(p, "%d %d %d %d %ld %ld %d %n", &idx, &b, &i, &s, &disp, &t, &kind, &n) != 7) break;
    p += n;
    for (int k = 0; k < 16; k++) { unsigned long long v; sscanf(p, "%llx %n", &v, &n); in.r[k] = v; p += n; }
    { unsigned long long v; sscanf(p, "%llx %n", &v, &n); in.fl = v; p += n; }
    sscanf(p, "%2047s %2047s", sh, sm);
    hex(sh, in.x, 256); hex(sm, buf, 512);
    if (b >= 0) {
      unsigned long a = (unsigned long)buf + t - disp - (i >= 0 ? in.r[i] * s : 0) - (kind ? fsb : 0);
      in.r[b] = a;
    }
    memset(&out, 0, sizeof out);
    if (sigsetjmp(jb, 1) == 0) {
      table[idx](&in, &out);
      printf("ok %lx %lx ", (unsigned long)buf, fsb);
      for (int k = 0; k < 16; k++) printf("%lx ", in.r[k]);
      for (int k = 0; k < 16; k++) printf("%lx ", out.r[k]);
      printf("%lx ", out.fl); phex(out.x, 256); printf(" "); phex(buf, 512); printf("\n");
    } else {
      printf("fault %lx %lx ", (unsigned long)buf, fsb);
      for (int k = 0; k < 16; k++) printf("%lx ", in.r[k]);
      printf("\n");
    }
    fflush(stdout);
  }
  return 0;
}
"""

def build(cases, tmp):
    regs = ["rax", "rcx", "rdx", "rbx", None, "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
    asm = [".text"]
    for k, (cls, text, patch) in enumerate(cases):
        a = [f".globl f_{k}", f"f_{k}:", "  push %rbx", "  push %rbp", "  push %r12", "  push %r13", "  push %r14", "  push %r15",
             "  mov %rsi, g_out(%rip)"]
        a += [f"  movdqu {136 + 16 * j}(%rdi), %xmm{j}" for j in range(16)]
        a += ["  pushq 128(%rdi)", "  popfq"]
        a += [f"  mov {8 * j}(%rdi), %{regs[j]}" for j in range(16) if regs[j] and regs[j] != "rdi"]
        a += ["  mov 56(%rdi), %rdi", f"i_{k}_s:", "  " + text, f"i_{k}_e:"]
        a += ["  pushfq", "  push %rax", "  mov g_out(%rip), %rax", "  popq 0(%rax)", "  popq 128(%rax)"]
        a += [f"  mov %{regs[j]}, {8 * j}(%rax)" for j in range(1, 16) if regs[j]]
        a += [f"  movdqu %xmm{j}, {136 + 16 * j}(%rax)" for j in range(16)]
        a += ["  pop %r15", "  pop %r14", "  pop %r13", "  pop %r12", "  pop %rbp", "  pop %rbx", "  ret"]
        asm += a
    asm += [".data", ".balign 8", "g_out: .quad 0", ".globl table", "table:"] + [f"  .quad f_{k}" for k in range(len(cases))]
    asm += ['.section .note.GNU-stack,"",@progbits']
    open(os.path.join(tmp, "forms.s"), "w").write("\n".join(asm) + "\n")
    open(os.path.join(tmp, "h.c"), "w").write(HARNESS_C)
    exe = os.path.join(tmp, "h")
    subprocess.run(["gcc", "-O1", "-no-pie", "-o", exe, os.path.join(tmp, "h.c"), os.path.join(tmp, "forms.s")], check=True)
    # instruction bytes, from the linked executable
    syms = {}
    for l in subprocess.run(["nm", exe], capture_output=True, text=True).stdout.splitlines():
        p = l.split()
        if len(p) == 3 and re.fullmatch(r"i_\d+_[se]", p[2]): syms[p[2]] = int(p[0], 16)
    sec = [l.split() for l in subprocess.run(["readelf", "-W", "-S", exe], capture_output=True, text=True).stdout.splitlines() if " .text " in l][0]
    k0 = sec.index(".text"); va, off = int(sec[k0 + 2], 16), int(sec[k0 + 3], 16)
    data = open(exe, "rb").read()
    return exe, [data[syms[f"i_{k}_s"] - va + off: syms[f"i_{k}_e"] - va + off] for k in range(len(cases))]

def main():
    cases = []
    for cls, f in templates():
        for _ in range(args.per):
            text, patch = f()
            cases.append((cls, text, patch))
    tmp = tempfile.mkdtemp()
    exe, insns = build(cases, tmp)
    lines = []
    for k, (cls, text, patch) in enumerate(cases):
        b, i, s, disp, t, kind = patch if patch else (-1, -1, 1, 0, 0, 0)
        regs = [rnd64() for _ in range(16)]
        if i >= 0: regs[i] = R.randrange(0, 16)
        if cls == "stosd": regs[1] = R.randrange(0, 9)   # rcx: element count
        fl = (R.getrandbits(12) & 0x8D5) | 0x202
        xmm = bytes(R.getrandbits(8) for _ in range(256))
        mem = bytes(R.getrandbits(8) for _ in range(512))
        if cls == "cmpxchg-eq":
            # the accumulator equals the destination, so the exchange happens
            regs[0] = int.from_bytes(mem[t:t + 8], "little")
        lines.append((k, b, i, s, disp, t, kind, regs, fl, xmm, mem))
    inp = "".join(f"{k} {b} {i} {s} {disp} {t} {kind} " + " ".join("%x" % r for r in regs) + f" {fl:x} {xmm.hex()} {mem.hex()}\n"
                  for (k, b, i, s, disp, t, kind, regs, fl, xmm, mem) in lines)
    res = subprocess.run([exe], input=inp, capture_output=True, text=True).stdout.splitlines()
    os.makedirs(args.out, exist_ok=True)
    nfault = 0
    with open(os.path.join(args.out, "cases.txt"), "w") as f:
        for (k, b, i, s, disp, t, kind, regs, fl, xmm, mem), r, (cls, text, _) in zip(lines, res, cases):
            p = r.split()
            bufa, fsb = int(p[1], 16), int(p[2], 16)
            rin = p[3:19]
            if p[0] != "ok":
                nfault += 1
                rout, flo, xo, mo = ["-"] * 16, "-", "-", "-"
            else:
                rout = p[19:35]; flo = p[35]; xo = p[36]; mo = p[37]
            # cmpxchg compares rax with memory: also run a variant where they are equal is not needed,
            # the harness reports what happened either way.
            f.write(" ".join([cls, text.replace(" ", "_"), insns[k].hex(), "%x" % bufa, "%x" % fsb] + rin +
                             ["%x" % fl, xmm.hex(), mem.hex()] + rout + [flo, xo, mo]) + "\n")
    print(f"{len(cases)} cases ({len(templates())} templates x {args.per}), {nfault} native faults (expected: the model has no step); "
          f"wrote {os.path.join(args.out, 'cases.txt')}")

main()
