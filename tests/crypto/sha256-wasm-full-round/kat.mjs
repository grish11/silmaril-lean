import { readFile } from "node:fs/promises";
import { deepStrictEqual, strictEqual } from "node:assert/strict";

const { instance } = await WebAssembly.instantiate(await readFile(process.argv[2]));
const { memory, sha256_round: round } = instance.exports;
const view = new DataView(memory.buffer);
const bytes = new Uint8Array(memory.buffer);

function check(dst, words, expected) {
  bytes.fill(0xa5);
  strictEqual(round(dst, ...words), undefined);
  const got = Array.from({ length: 8 }, (_, i) => view.getUint32(dst + 4 * i, true));
  deepStrictEqual(got, expected);
  strictEqual(memory.buffer, bytes.buffer);
  strictEqual(bytes.subarray(0, dst).every(byte => byte === 0xa5), true);
  strictEqual(bytes.subarray(dst + 32).every(byte => byte === 0xa5), true);
}

// NIST SHA256.pdf, pp. 1–2, the first two "abc" working states.
const initial = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];
const first = [
  0x5d6aebcd, 0x6a09e667, 0xbb67ae85, 0x3c6ef372,
  0xfa2a4622, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
];
const second = [
  0x5a6ad9ad, 0x5d6aebcd, 0x6a09e667, 0xbb67ae85,
  0x78ce7989, 0xfa2a4622, 0x510e527f, 0x9b05688c,
];
check(0, [...initial, 0x428a2f98, 0x61626380], first);
check(bytes.length - 32, [...first, 0x71374491, 0], second);
console.log("Native WebAssembly matched 16 published working words at both memory boundaries");

// Differential cases use the FIPS equations and independent JS bitwise operations.
const rotr = (x, n) => (x >>> n) | (x << (32 - n));
function reference([a, b, c, d, e, f, g, h, k, w]) {
  const sum0 = (rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) >>> 0;
  const sum1 = (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) >>> 0;
  const choose = ((e & f) ^ (~e & g)) >>> 0;
  const majority = ((a & b) ^ (a & c) ^ (b & c)) >>> 0;
  const t1 = (h + sum1 + choose + k + w) >>> 0;
  return [(t1 + sum0 + majority) >>> 0, a, b, c, (d + t1) >>> 0, e, f, g];
}

let state = 0xc3;
function next() {
  state ^= state << 13;
  state ^= state >>> 17;
  state ^= state << 5;
  return state >>> 0;
}
for (let i = 0; i < 128; i++) {
  const words = Array.from({ length: 10 }, next);
  check(16 + 4 * i, words, reference(words));
}
console.log("128 deterministic differential cases preserved all bytes outside the output");
