// make.fun tiny-stack-vm-01, built from ISA.md version 1.
//
// For every <input>/<id>/program.bin with its input.bin, write
// <output>/<id>/stdout.bin (the bytes the program wrote) and exit.txt (its
// exit code in decimal).
//
// Step order is the spec's: step budget, pc bounds, known opcode, immediate
// fits, stack needs (underflow, then overflow), the instruction's own traps,
// the effect. A trap keeps earlier output; the trapping instruction writes
// nothing.

import fs from "node:fs";
import path from "node:path";

const MAX_STEPS = 1_000_000;
const MAX_OUT = 65_536;

// Ops that pop `arity` values and push one. Args are (a, b), a deeper; the
// result is 32 bits. NaN stands for division by zero (trap 4).
const ALU = {
  0x10: (a, b) => (a + b) | 0,
  0x11: (a, b) => (a - b) | 0,
  0x12: (a, b) => Math.imul(a, b), // low 32 bits of the exact product
  0x13: (a, b) => (b ? Math.trunc(a / b) | 0 : NaN), // signed, toward zero
  0x14: (a, b) => (b ? (a % b) | 0 : NaN), // remainder signed like a
  0x15: (a, b) => (b ? Math.floor((a >>> 0) / (b >>> 0)) | 0 : NaN),
  0x16: (a, b) => (b ? ((a >>> 0) % (b >>> 0)) | 0 : NaN),
  0x17: (a) => -a | 0, // wraps: -(-2147483648) is itself
  0x18: (a, b) => a & b,
  0x19: (a, b) => a | b,
  0x1a: (a, b) => a ^ b,
  0x1b: (a) => ~a,
  0x1c: (a, b) => a << (b & 31), // only the count's low 5 bits count
  0x1d: (a, b) => a >> (b & 31), // arithmetic: the sign bit is copied in
  0x1e: (a, b) => (a >>> (b & 31)) | 0, // logical, read back as signed
  0x20: (a, b) => +(a === b),
  0x21: (a, b) => +(a < b), // signed
  0x22: (a, b) => +((a >>> 0) < (b >>> 0)), // unsigned
};

// Everything else: [popped, pushed, immediate bytes]. Unknown traps 5.
const OPS = {
  0x00: [0, 0, 0], // HALT, exit 0
  0x01: [0, 1, 1], // PUSH8, sign-extended byte
  0x02: [0, 1, 4], // PUSH32, little-endian
  0x03: [1, 0, 0], // POP
  0x04: [1, 2, 0], // DUP
  0x05: [2, 2, 0], // SWAP ( a b -- b a )
  0x06: [2, 3, 0], // OVER ( a b -- a b a )
  0x07: [3, 3, 0], // ROT  ( a b c -- b c a )
  0x30: [0, 0, 2], // JMP, signed offset from the next instruction
  0x31: [1, 0, 2], // JZ
  0x32: [1, 0, 2], // JNZ
  0x33: [0, 0, 2], // CALL, unsigned absolute address
  0x34: [0, 0, 0], // RET
  0x40: [1, 1, 0], // LOAD
  0x41: [2, 0, 0], // STORE ( v addr -- )
  0x50: [1, 0, 0], // PRINT, decimal ASCII
  0x51: [1, 0, 0], // PUTC, v & 255
  0x52: [0, 1, 0], // IN, -1 when the input is used up
  0x53: [1, 0, 0], // EXIT, v & 255
};
for (const k in ALU) OPS[k] = [ALU[k].length, 1, 0];

function run(prog, input) {
  const st = []; // data stack, at most 256
  const cs = []; // call stack, at most 64
  const mem = new Int32Array(256);
  const out = Buffer.alloc(MAX_OUT);
  let outLen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  let code = -1;

  while (code < 0) {
    if (steps === MAX_STEPS) return { out, outLen, code: 10 };
    if (pc < 0 || pc >= prog.length) return { out, outLen, code: 9 };
    const op = prog[pc];
    const sig = OPS[op];
    if (!sig) return { out, outLen, code: 5 };
    const next = pc + 1 + sig[2];
    if (next > prog.length) return { out, outLen, code: 9 };
    if (st.length < sig[0]) return { out, outLen, code: 2 };
    if (st.length - sig[0] + sig[1] > 256) return { out, outLen, code: 3 };
    steps++;
    const imm = pc + 1;
    const off = ((prog[imm] | (prog[imm + 1] << 8)) << 16) >> 16;
    let a, b;

    switch (op) {
      case 0x00: code = 0; break;
      case 0x01: st.push((prog[imm] << 24) >> 24); pc = next; break;
      case 0x02: st.push(prog[imm] | (prog[imm + 1] << 8) | (prog[imm + 2] << 16) | (prog[imm + 3] << 24)); pc = next; break;
      case 0x03: st.pop(); pc = next; break;
      case 0x04: st.push(st[st.length - 1]); pc = next; break;
      case 0x05: b = st.pop(); a = st.pop(); st.push(b, a); pc = next; break; // SWAP
      case 0x06: st.push(st[st.length - 2]); pc = next; break; // OVER
      case 0x07: { // ROT: ( a b c -- b c a )
        const c = st.pop();
        const ab = st.pop();
        const aa = st.pop();
        st.push(ab, c, aa);
        pc = next;
        break;
      }
      case 0x30: pc = next + off; break;
      case 0x31: pc = st.pop() === 0 ? next + off : next; break;
      case 0x32: pc = st.pop() !== 0 ? next + off : next; break;
      case 0x33:
        if (cs.length === 64) return { out, outLen, code: 7 };
        cs.push(next);
        pc = prog[imm] | (prog[imm + 1] << 8);
        break;
      case 0x34:
        if (!cs.length) return { out, outLen, code: 8 };
        pc = cs.pop();
        break;
      case 0x40:
        a = st.pop();
        if (a < 0 || a > 255) return { out, outLen, code: 6 };
        st.push(mem[a]);
        pc = next;
        break;
      case 0x41:
        b = st.pop(); // address
        a = st.pop(); // value
        if (b < 0 || b > 255) return { out, outLen, code: 6 };
        mem[b] = a;
        pc = next;
        break;
      case 0x50: {
        const s = String(st.pop());
        if (outLen + s.length > MAX_OUT) return { out, outLen, code: 11 };
        outLen += out.write(s, outLen, "latin1");
        pc = next;
        break;
      }
      case 0x51:
        if (outLen === MAX_OUT) return { out, outLen, code: 11 };
        out[outLen++] = st.pop() & 255;
        pc = next;
        break;
      case 0x52: st.push(ip < input.length ? input[ip++] : -1); pc = next; break;
      case 0x53: code = st.pop() & 255; break;
      default: {
        const f = ALU[op];
        if (f.length === 1) {
          st.push(f(st.pop()));
        } else {
          b = st.pop();
          a = st.pop();
          const r = f(a, b);
          if (r !== r) return { out, outLen, code: 4 };
          st.push(r);
        }
        pc = next;
      }
    }
  }
  return { out, outLen, code };
}

const inRoot = process.env.MAKEFUN_INPUT_DIR || "/input";
const outRoot = process.env.MAKEFUN_OUTPUT_DIR || "/output";
for (const id of fs.readdirSync(inRoot).sort()) {
  const src = path.join(inRoot, id);
  const progPath = path.join(src, "program.bin");
  if (!fs.existsSync(progPath)) continue;
  const inPath = path.join(src, "input.bin");
  const r = run(
    fs.readFileSync(progPath),
    fs.existsSync(inPath) ? fs.readFileSync(inPath) : Buffer.alloc(0),
  );
  const dst = path.join(outRoot, id);
  fs.mkdirSync(dst, { recursive: true });
  fs.writeFileSync(path.join(dst, "stdout.bin"), r.out.subarray(0, r.outLen));
  fs.writeFileSync(path.join(dst, "exit.txt"), r.code + "\n");
}
