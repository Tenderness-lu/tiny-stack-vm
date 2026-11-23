// Tiny stack VM: exact implementation of make.fun's ISA v1 (see kit ISA.md / vm.mjs).
// Runs every /input/<id> program and writes /output/<id>/stdout.bin + exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// opcode -> [immediate bytes, pops, pushes]; absent = unknown opcode (trap 5)
const T = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0], 4: [0, 1, 2],
  5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3],
  16: [0, 2, 1], 17: [0, 2, 1], 18: [0, 2, 1], 19: [0, 2, 1], 20: [0, 2, 1],
  21: [0, 2, 1], 22: [0, 2, 1], 23: [0, 1, 1], 24: [0, 2, 1], 25: [0, 2, 1],
  26: [0, 2, 1], 27: [0, 1, 1], 28: [0, 2, 1], 29: [0, 2, 1], 30: [0, 2, 1],
  32: [0, 2, 1], 33: [0, 2, 1], 34: [0, 2, 1],
  48: [2, 0, 0], 49: [2, 1, 0], 50: [2, 1, 0], 51: [2, 0, 0], 52: [0, 0, 0],
  64: [0, 1, 1], 65: [0, 2, 0], 80: [0, 1, 0], 81: [0, 1, 0], 82: [0, 0, 1], 83: [0, 1, 0],
};

// Machine limits from ISA.md: 256-value data stack, 64-deep call stack,
// 256-word memory, 1,000,000 steps, 65,536 output bytes.
const STACK_MAX = 256, CALL_MAX = 64, MEM_SIZE = 256;
const STEP_LIMIT = 1000000, OUT_LIMIT = 65536;
const OUT = new Uint8Array(OUT_LIMIT); // shared output buffer, sliced per instance

// Returns [output length, exit code].
function run(p, q) {
  const n = p.length, D = new Int32Array(STACK_MAX), C = new Int32Array(CALL_MAX), M = new Int32Array(MEM_SIZE);
  let s = 0, c = 0, ol = 0, ip = 0, pc = 0, st = 0;
  for (;;) {
    if (st === STEP_LIMIT) return [ol, 10];
    if (pc < 0 || pc >= n) return [ol, 9];
    const op = p[pc], t = T[op];
    if (!t) return [ol, 5];
    const im = t[0];
    if (pc + im >= n) return [ol, 9];
    st++;
    const nx = pc + 1 + im;
    if (s < t[1]) return [ol, 2];
    if (s - t[1] + t[2] > STACK_MAX) return [ol, 3];
    pc = nx;
    switch (op) {
      case 0: return [ol, 0];
      case 1: D[s++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[s++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: s--; break;
      case 4: D[s] = D[s - 1]; s++; break;
      case 5: { const v = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = v; break; }
      case 6: D[s] = D[s - 2]; s++; break;
      case 7: { const v = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = v; break; }
      case 23: D[s - 1] = -D[s - 1] | 0; break;
      case 27: D[s - 1] = ~D[s - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[s - 1], a = D[s - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (b === 0) return [ol, 4]; r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (b === 0) return [ol, 4]; r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 21) { if (b === 0) return [ol, 4]; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (b === 0) return [ol, 4]; r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        s -= 2; D[s++] = r; break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = D[--s]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (c === CALL_MAX) return [ol, 7];
        C[c++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 52:
        if (c === 0) return [ol, 8];
        pc = C[--c]; break;
      case 64: {
        const a = D[s - 1];
        if (a < 0 || a >= MEM_SIZE) return [ol, 6];
        D[s - 1] = M[a]; break;
      }
      case 65: {
        const a = D[s - 1], v = D[s - 2];
        if (a < 0 || a >= MEM_SIZE) return [ol, 6];
        s -= 2; M[a] = v; break;
      }
      case 80: {
        const g = String(D[s - 1]);
        if (ol + g.length > OUT_LIMIT) return [ol, 11];
        s--;
        for (let i = 0; i < g.length; i++) OUT[ol++] = g.charCodeAt(i);
        break;
      }
      case 81:
        if (ol + 1 > OUT_LIMIT) return [ol, 11];
        OUT[ol++] = D[--s] & 255; break;
      case 82: D[s++] = ip < q.length ? q[ip++] : -1; break;
      case 83: return [ol, D[--s] & 255];
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), OUT.subarray(0, r[0]));
  writeFileSync(join(O, id, 'exit.txt'), r[1] + '\n');
}
