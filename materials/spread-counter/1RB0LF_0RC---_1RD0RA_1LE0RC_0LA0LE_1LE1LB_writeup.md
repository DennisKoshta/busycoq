# 1RB0LF_0RC---_1RD0RA_1LE0RC_0LA0LE_1LE1LB: never halts

This machine stores a binary counter whose digits are separated by variable gaps. Most bounces increment it; some overflows trigger a long pause that rebuilds those gaps.

A finite description of the tail and an interval invariant prove that every pause and increment can continue.

```
     0    1
A   1RB  0LF
B   0RC  ---        halting transition: B reads 1
C   1RD  0RA
D   1LE  0RC
E   0LA  0LE
F   1LE  1LB
```

## 0. Overview

The tape right of the head is a binary counter written in three tokens, `00`, `01` and `Z = 100`.

A digit is `b Z 01 Z^g`, where `b` is `00` (bit 0) or `01` (bit 1) and `g` is the gap to the next digit.

The head bounces off the left end, and every bounce adds 1 to the counter (rule Inc, §2).

At the right end of the counter there is a block of gap-1 digits (the R block) followed by a finite-state "tail" W. When the counter overflows, the carry runs into the tail.

The tail answers in one of two ways:

- **S (silent):** the counter wraps to 0 and nothing else happens.

- **N:** the whole left part of the tape freezes into a "wall". The machine then spends a long pause eating the wall two increments at a time (§3), rebuilding every gap exactly and possibly inserting new digits.

The proof has four layers:

1. Window lemmas and the parametric counter rules (§2–§3).

2. The overflow (§4): a right sweep to the first 0 bit of the tail, then a leftward return. The return is a 4-rule transducer on the tokens the sweep left behind.

On the tail, its result depends only on where the tail's first 0 bit is (14 cases, plus an induction for the tail's growing end unit).

Over the R block, its parity decides N or S.

3. TAILFRONT (§4.5): the tail's 2-bit front unit cycles `10 → 01 → 11 → 00 → 10`, and S can only happen at `11`.

4. Linear arithmetic on the counter parameters (§5): an interval invariant at normal-mode overflows that holds whatever the tail chooses at each `11` slot.

## 1. Notation and families

### 1.1 Tape notation

- `0^inf u X> v 0^inf`: state X reads the first cell of v. `u <X v`: state X reads the last cell of u.

- Window lemma `u <X v → <Y u'v'` (or `→ u'v' Y>`): started with the head on the last cell of u (or the first cell of v), the run stays inside the |u|+|v| cells and leaves them on the stated side in state Y.

Such a lemma holds in every context.

- **Tokens.** Right of the lead, the tape is read as a word over `00`, `01` and `Z = 100`. A right sweep in state C leaves **processed** tokens behind: `00` and `01` become `10`, and `Z` becomes `010`.

- **Inner record (IR):** A reads a 0 that it reached moving left, and the cells from the head on read `(001)^p 00 0b10001`.

All macro rules go from one IR to the next. Note that `(001)^p 00 = 00 Z^p`.

- `Z = 100`. A **digit** is `d(b) = 0b10001 = b' Z 01` with b' = `0b`. A **counter** is
  `D_G(v) = d(b_0) Z^(g_1) d(b_1) Z^(g_2) ... d(b_(N-1))`, with v = Σ b_i 2^i (LSB leftmost).

- `Zn(g) := (010)^(g+1)` is a **zone**: a gap g frozen into the wall.

### 1.2 The right counter RC and the tail

- At every configuration we use, the counter has this form:

  - k ≥ 0 **large-gap digits** d_0..d_(k-1), with gaps G = (g_1..g_k), every g_i ≥ 7;

  - then the **gap-2 digit**, followed by the gap `Z^2`;

  - then the **R block** `U^q`, where U = `01100` = `01 Z` and q = 2r + H. In digit terms this is r gap-1 digits `0110001100` plus a half digit H ∈ {0,1}.

  - The number of counter digits is N = k + 1 + r + H.

- The **tail** is `W(f, e) := F(f) (0e_1)(0e_2)...(0e_m) 01`, where
  `F(f) = 0x0y0z10001 0?0?10001 0?1000?10001 0?0?1000?10001 0?1000?1000?1000?1000?10001` (11 + 9 + 12 + 14 + 27 = 73 cells: 15 bit cells and 58 fixed cells).

  - f is the 15 bits at the `?` places, read left to right; x, y, z are the first three of them, and b4, ..., b15 are the other twelve.

  - The end unit has m ≥ 0 bits e_1..e_m and the end marker `01`.

  - The **front unit** is (y, z).

  - In tokens, every bit is a token `0b`, and the fixed cells are tokens `Z` and `01`.

- **L\*** := the tails with x = 1 and H = y.

### 1.3 Families

- `K_N(a; D; RC) := 0^inf A>(001)^a 00 D RC` (normal mode, lead a).

- `K_P(Wall; p; D; RC) := 0^inf Wall A>(001)^p 00 D RC` (pause mode, inner lead p).

- **X(a; G; r, H; f, e)** := K_N(a; all bits 1; ...) with the counter of §1.2 and a tail in L\*. This is a normal-mode overflow configuration:
  `0^inf A>(001)^a 00 [0110001 Z^(g_i)]_(i=1..k) 0110001 Z^2 U^(2r+H) W(f, e)`.

- **The invariant set** is the configurations X that satisfy INV (§5.3).

## 2. Window lemmas and the counter

### 2.1 Window lemmas
Each row is one finite run that never reads outside its window, so it holds in every context. The last column names the lemma of the .v;

a dot is composition. Step counts are given for orientation; the .v does not track them.

| name | lemma | steps | in the .v |
|---|---|---|---|
| R2 | `A> 00 → 10 C>` | 2 | `AT0` |
| R4 | `C> 100 → 010 C>` | 3 | `CTZ` |
| R6 | `C> 01 → 10 C>` | 2 | `CT1` |
| R7 | `C> 00 → <E 01` | 3 | `CT0` |
| R3 | `C> 0110001 → 1001010 C>` (a 1-digit) | 7 | `CT1`·`CTZ`·`CT1` |
| R5 | `C> 0010001 → <E 0110001` (a 0-digit is set) | 3 | `CT0` |
| L1 | `010 <E → <E 100` | 3 | `EPZ` |
| L2 | `1001010 <E → <E 0010001` (a processed 1-digit is reset) | 17 | `EP`·`FPZP` |
| L3 | `10 <E → <F 00` | 2 | `EP` |
| L3F | `10 <F → <E 01` | 2 | `FP` |
| L4 | `100 <F → <F 001` | 3 | inside `ENDZX` |
| UE | `10010 <E → <F 00100` | 5 | `EPZ`·`EP` |
| UF | `10010 <F 00 → <E 00100 01` | 15 | `FPZP` |
| PE = UE·UF | `1001010010 <E → <E 0010001100` | 20 | `RB_E2` with n = 1 |
| PF = UF·UE | `1001010010 <F 00 → <F 0010000100 01` | 20 | `RB_F2` with n = 1 |
| END | `00 <F → <A 01` | 2 | `ENDl`; at the left edge `Bnc` |
| B1 | `01 <F → 00 A>` | 3 | `B1` |
| ENDZX | `010010100100 <F → <A 000100011001` | 22 | `ENDZX` |
| BN | `010010 <F 00 → <A 00010001` | 16 | `BN` |
| BS | `1001010010010 <E → <E 0010001100100` | 23 | `EPZ`·`EPZ`·`EP`·`FPZP` (the transducer of §4.2) |
| CF1 | `C> F(1^15) → P1 C>` (P1 = the 73-cell image) | 73 | `Csweep` |
| PEN | `P1 <E → <E F(100100010001010)` | 133 | `F1E_ret` (the transducer) |
| PFN | `P1 <F → <F F(010000100100101)` | 123 | `F1F_ret` (the transducer) |

PEN and PFN are 73-cell windows: neither run reads the cell right of P1, so whatever lies there (the end unit) is left unchanged.

Shift rules, by induction from R4 and L1: `C> Z^n → (010)^n C>` (3n steps, `CTZs`) and `(010)^n <E → <E Z^n` (3n, `EPZs`), both through the framework's `shift_rule_R`/`shift_rule_L`.

More generally, C passes any token word without a `00` and processes it (`Csweep`, by induction on the word). R2 followed by R4^a is the shift `A> (001)^a 00 → (100)^a 10 C>`.

### 2.2 Rule Inc_L
**Inc_L.** For every left half-tape L, every a ≥ 0 and every counter D_G(v) with v + 1 < 2^N:

`L A>(001)^a 00 D_G(v) T  →  L <F (001)^a 00 D_G(v+1) T`, in 6a + 6S_j + 24j + 7 steps.

Here j = the number of trailing 1 bits of v (b_0..b_(j-1) = 1, b_j = 0) and S_j = g_1 + ... + g_j. The head never reads L before the last step, so L is arbitrary.

T is arbitrary too, because the run never reads past d_j.

Proof, in order:

1. R2, R4^a.

2. For i = 0..j-1: R3 on d_i, then R4^(g_(i+1)).

3. R5 on d_j.

4. For i = j-1 down to 0: L1^(g_(i+1)), then L2 on the processed d_i.

5. L1^a, then L3.

The step total is 2 + 3a + Σ(7 + 3g) + 3 + Σ(3g + 17) + 3a + 2. The proof is by induction on the carry depth j, like `Climb`/`E_stmt` in CounterClass3v2 TM1. In the .v the counter is `ctr gs v` (a list of gaps, LSB first, whose last digit is its bit only, so the digits above the carry are never read), the induction is `IncC` (over the list `gs`), and `IncL` adds steps 1 and 5.

### 2.3 Rule Inc
**Inc.** `K_N(a; D_G(v); T) → K_N(a+1; D_G(v+1); T)` for v + 1 < 2^N, in 6a + 6S_j + 24j + 9 steps.

Proof: Inc_L with L = 0^inf, then END. `0^inf 00 <F → 0^inf <A 01` leaves A reading a 0 that it reached moving left, with `0 01 (001)^a 00 = (001)^(a+1) 00` on its right.

In the .v: `Inc`, and on the IR family `Inc1`, iterated as `Incs`.

## 3. Pause rules

Each pause rule has the shape Inc_L, then (if two increments) B1 and Inc_L again, then a left-end lemma that ends at the next IR.

In every rule b_0 = 0 (v even), so the first Inc_L has j = 0 (6p + 7 steps). j and S below belong to the second increment.

| rule | statement (IR → IR) | domain | steps | proof |
|---|---|---|---|---|
| P100 | `(100)^(n+1) 1 A>(001)^p 00 D(v) → (100)^n 1 A>(001)^(p+1) 00 D(v+2)` | n ≥ 0, v+2 < 2^N | 12p+6S+24j+19 | Inc_L, B1, Inc_L, END |
| WX | `0^inf 1 A>(001)^p 00 D(v) → 0^inf A>(001)^(p+1) 00 D(v+2)` (normal mode again) | v+2 < 2^N | same | Inc_L, B1, Inc_L, END |
| P010 | `Y (010)^(m+1) 01 A>(001)^p 00 D(v) → Y (010)^m 01 A>(001)^(p+1) 00 D(v+2)` | m ≥ 0, any Y | same | Inc_L, B1, Inc_L, END |
| ZX | `Y (010)^h 1001 01 A>(001)^p 00 D_G(v) → Y (010)^(h-3) 01 A>00 D_(p+2,G)(2(v+2))` | h ≥ 3, any Y | 12p+6S+24j+39 | Inc_L, B1, Inc_L, ENDZX |
| ZXN | `(100)^n 10100101 A>(001)^p 00 D_G(v) → (100)^(n-2) 1 A>00 D_(p+2,G)(2(v+2))` | n ≥ 2 | 12p+6S+24j+39 | as ZX |
| ZXP1 | `(100)^n 01 A>(001)^p 00 D(v) → (100)^(n-1) 10 A>(001)^(p+1) 00 D(v+2)` | n ≥ 1 | 12p+6S+24j+19 | Inc_L, B1, Inc_L, END |
| ZXP2 | `(100)^n 10 A>(001)^p 00 D_G(v) → (100)^(n-2) 1 A>00 D_(p,G)(2(v+1))` | n ≥ 2, v even | 6p+23 | Inc_L (j=0), BN |

`D_(g,G)(2u)` is the counter with a new LSB digit 0 at gap g in front of the old digits, so its value is 2u.

In ZX/ZXN the second Inc_L ends with F on the last cell of a wall that ends `...010 010 100 100` (ZX) or `...0 100 10100100` (ZXN).

In both cases the last 12 cells are `010010100100`, and ENDZX (22 steps, L4 twice inside it) turns them into `000100011001`.

A then reads the 13th cell from the end, which is 0, so this is an IR. That needs h ≥ 3 (ZX) or n ≥ 2 (ZXN). The right side reads `0 000100011001 (001)^p 00 d_0...` = `00 0010001 Z^(p+2) d_0...`, because `1001 (001)^p 00 = Z^(p+2)`.

ZXP2 ends with BN on the last 6 cells `010010` of `(100)^n 10` plus the `00` of the first `001`. A then reads the middle cell of block n−1, so n ≥ 2 is needed.

The domains above are wider than what the run needs: Y and the walls are arbitrary words of the stated shape. In the .v the seven rules are three generic lemmas over an arbitrary left part L, and each wall shape is a choice of L:

- `TwoInc` (Inc_L, B1, Inc_L, END) gives P100, WX, P010 and ZXP1;

- `ZXg` (Inc_L, B1, Inc_L, ENDZX) gives ZX and ZXN;

- `ZXP2g` (Inc_L, BN) gives ZXP2.

On the IR family `KP W p gs v H St`, W is the wall, p the inner lead, `ctr gs v` the counter, `sfx H` the R-block end, and St the tail. The case W = 0^inf is normal mode.

The corresponding lemmas are:

```
P100 / P100s
WX
P010s
Zone / Zones
ZXN
ZXP (ZXP1 then ZXP2)
```

## 4. The overflow

### 4.1 Right sweep (OvR)
Start from X(a; G; r, H; f, e), or from the second increment of a P-cycle in pause mode at an overflow slot (wall `(100)^n 1` with n ≥ 1, which is `(100)^(n-1) 1000` after B1).

The carry passes every digit:

R2, R4^a, [R3, R4^(g_i)] for i = 1..k, R3 (gap-2 digit), R4^2, then (R6, R4)^q over the R block.

C now stands on the first cell of F(f), and every token to its left is processed: `00→10`, `01→10`, `Z→010`. In particular the gap-2 digit is now `1001010 010010` and each of the q units U = `01100` is now P := `10010`.

In the .v this is `OvSweep` (R2, then `Csweep`, since the all-ones counter contains no `00` token).

### 4.2 The tail's answer: the return transducer
Write T(f) for what the machine does next, as a function of the 15 bits f (in L\*, x = 1, so there are 2^14 = 16,384 settings).

T(f) is not tabulated case by case. It follows from two facts.

**First zero.** C keeps going over the tail: R6 passes every `01`, R4 passes every `Z`, and the first `00` token stops it, R7 `C> 00 → <E 01`.

In the tail the `00` tokens are exactly the 0 bits. So C stops at the first 0 bit of f, at a position i ≥ 2 (x = 1), and never reaches the end unit unless f = 1^15 (§4.4).

All bits before position i are 1, so the processed word left of the head depends only on i, on the R block and on the left part.

**The return transducer.** Moving left, the machine now runs a transducer on processed tokens. The head is on the last cell of a processed token, in mode E or F:

| mode, processed token(s) left of the head | lemma | the tokens become | new mode |
|---|---|---|---|
| E, `010` | L1 `010 <E → <E 100` | `Z` | E |
| E, `10` | L3 `10 <E → <F 00` | `00` | F |
| F, `10` | L3F `10 <F → <E 01` | `01` | E |
| F, `10 010` with the token `00` on the right | UF `10010 <F 00 → <E 00100 01` | `00 Z`, and the `00` on the right becomes `01` | E |

It stops when no row applies. In the .v this is the function `retf` on token lists, with soundness lemma `retf_spec`: whatever `retf` computes, the machine does.

The proof is by induction on a length bound, because the UF row eats two tokens. `retf_app` composes two runs.

**The answer depends only on i.** The return starts in mode E over the processed prefix of the tail, so its outcome on the tail is one of 14 fixed computations, one per position of the first 0 (`TailRet`;

the lemmas `Tail0z`, `Tail10` and the 12 cases of `Tail11`, each closed by computing `retf`). The table lists them. "Returns in" is the mode in which the head leaves the tail on the left.

f' is the 15-bit part after the whole overflow. When the tail returns in F, the cells right of the head are `00` (the token x), and the R-block return of §4.3 (a UF, or BN) turns them into `01`, so x' = 1 in every row.

The class is N or S as derived in §4.3 (it uses H = y).

| front (y, z) | first 0 at | returns in | f' | class |
|---|---|---|---|---|
| 0z | y | F | `11z` b4..b15 | N, e1 |
| 10 | z | E | `101` b4..b15 | N, e0 |
| 11 | b4 | E | `1001` b5..b15 | N, e0 |
| 11 | b5 | F | `11001` b6..b15 | S |
| 11 | b6 | F | `110001` b7..b15 | S |
| 11 | b7 | E | `1001001` b8..b15 | N, e0 |
| 11 | b8 | E | `10010001` b9..b15 | N, e0 |
| 11 | b9 | F | `110000101` b10..b15 | S |
| 11 | b10 | E | `1001000101` b11..b15 | N, e0 |
| 11 | b11 | E | `10010001001` b12..b15 | N, e0 |
| 11 | b12 | F | `110000100101` b13..b15 | S |
| 11 | b13 | E | `1001000100011` b14 b15 | N, e0 |
| 11 | b14 | F | `11000010010011` b15 | S |
| 11 | b15 | E | `100100010001011` | N, e0 |
| 11 | none (f = 1^15) | §4.4 | `100100010001010` or `110000100100101` | N, e0 or S |

The bits after the first 0 are unchanged. Every N row from front 11 lands on front 00, and every S row lands on front 10. The tail is in effect a small mixed-radix counter;

the proof needs only the front unit, and both answers at front 11 are covered.

### 4.3 Return through the R block (lemma RB), and the boundary
After OvR and the tail's return (f ≠ 1^15), the head is on the last cell of `P^q` in state σ (the mode the tail returned in), with the tail's output and the untouched end unit on its right.

If σ = F, the cells right of the head are `00`. Left of `P^q` is the processed gap-2 digit `1001010 010010`.

**Lemma RB.** Let σ ∈ {E, F}, q ≥ 0, and let w be any word that starts with `00` if σ = F. Number the units 1..q from the left, and let μ_i be the mode in which unit i is entered: μ_q = σ and μ_i = flip(μ_(i+1)).

Let μ := flip(μ_1) = σ flipped q times (μ = σ if q = 0). Then

`P^q <σ w  →  <μ u_1 u_2 ... u_q w*`, in Σ_i (5 if μ_i = E, 15 if μ_i = F) steps, where

- u_i = t_i `100`, with t_1 = `00`, and for i ≥ 2, t_i = `01` if μ_(i−1) = F and `00` if μ_(i−1) = E;

- w* = w with its first token replaced by `01` if q ≥ 1 and σ = F, and w* = w otherwise.

*Proof*, by induction on q. For q = 0 there is nothing to do. For q + 1, the first lemma applied is to the rightmost unit:

- **σ = E:** UE `10010 <E → <F 00100` leaves `P^q <F 00100 w`. The new right word `00100 w` starts with `00`, so the induction hypothesis applies with mode F.

It gives units 1..q, turns the first token of `00100` into `01` if q ≥ 1 (so t_(q+1) = `01` exactly when μ_q = F, as claimed), and leaves w unchanged (w* = w, as claimed for σ = E).

- **σ = F:** w = `00 w'` by assumption. UF `10010 <F 00 → <E 00100 01` leaves `P^q <E 00100 01 w'`. The hypothesis applies with mode E, which has no precondition.

It gives units 1..q and does not touch its right word, so u_(q+1) = `00100` (t_(q+1) = `00`, matching μ_q = E) and w* = `01 w'` (matching σ = F).

In both cases the mode flips once more, so the final mode is σ flipped q + 1 times. ∎

So the `00`-on-the-right precondition of every UF is carried by the induction: inside the block it is the `00100` just written by UE, and at the right end it is the `00` that a tail returning in F leaves in front of itself (§4.2).

In the .v, lemma RB is four closed forms of the transducer, each by induction on the number of unit pairs: `RB_E2` and `RB_F2` (an even number of units, entered in E or F) and `RB_E1` and `RB_F1` (an odd number).

**The boundary.** μ = F gives N and μ = E gives S.

- **μ = F → N.** The two cells right of the head are `00`: the token t_1 = `00` of u_1 if q ≥ 1, or the first token of w* if q = 0 (then σ = μ = F, and the tail left `00`).

BN `010010 <F 00 → <A 00010001` rewrites the processed `Z Z` and that token. A then reads the last cell of the processed gap-2 digit `1001010`, which is 0, so this is an IR with lead 0. Reading the cells from A: `0 000100 01 ...` = `00 | 00100 | 01 ...`.

  - BN therefore **re-tokenises** the processed gap-2 digit. Its first 6 cells `100101` join the wall, its 7th cell and the first cell of BN's output form the lead `00`, and the next 5 cells form a new unit u_0 = `00100`.

  - BN also sets t_1 to `01`, or the first token of w* when q = 0. This is why the R block grows leftward.

  - From normal mode this is rule **NO**:
    `X(a; G; r, H; f, e) → 0^inf (100)^a 101001 [Zn(g_i) 1001]_(i=1..k) 01 A> 00 RC'`.
    This is just the processed left part read as a wall: `(100)^a 10 [1001010 (010)^(g_i)]_i 100101` (`wallOv` in the .v).

  - From pause mode (n ≥ 1) it is rule **PO**:
    `0^inf (100)^n 1 A>(001)^p 00 D(2^N-2) RC → 0^inf (100)^n Zn(p) 1001 [Zn(g_i) 1001]_i 01 A> 00 RC'`.
    This comes from Inc_L(j = 0), B1, then OvR with left context `(100)^(n-1) 1000` (`wallPO`).

- **μ = E → S.** The transducer goes on. Over the processed gap-2 digit it is BS `1001010010010 <E → <E 0010001100100`, which restores that digit with bit 0. Over each processed large digit it is [L1^(g_i), L2], for i = k..1, and over the lead it is L1^a and then L3, as in Inc_L.

Each digit is restored with bit 0, and F stops on the cell left of the lead (`retf_dig`, `retf_LD`, `retf_lead`).

  - From normal mode, END gives rule **SILENT**: `X(...) → K_N(a+1; D_G(0); RC')` with the gap-2 digit kept. The counter wraps and there is no pause.

  - From pause mode, END gives rule **SILENTP**: `(100)^n 1 A>(001)^p 00 D(2^N-2) → (100)^(n-1) 1 A>(001)^(p+1) 00 D(0)`, for n ≥ 1.

**The new right counter RC'** (the word after the lead `00`, minus the gap-2 digit, which is rebuilt by the first ZX after N and kept after S).

Write q = 2r + H. From RB, μ_i alternates.

- **N** (μ = F, so μ_1 = E): RC' = u_0 u_1 ... u_q w**. The first tokens are `00` at even indices and `01` at odd indices (u_0 = `00100`, t_1 set to `01` by BN, and for i ≥ 2, t_i = `01` iff μ_(i−1) = F iff i is odd).

The first token of w** is `01` if q is even (σ = μ_q = F, and the UF on u_q, or BN when q = 0, set it) and is the tail's own first token if q is odd (σ = E, and §4.2's table keeps x = 1).

Either way the tail now starts with `01`, so x' = 1.

  - The pairs (u_0 u_1), (u_2 u_3), ... are `00100 01100` = `0010001 100` = d(0) Z, R digits with bit 0 at gap 1.

  - **q odd** (H = 1): q + 1 units pair up, so r' = (q+1)/2 = r + 1 and H' = 0, and the tail follows.

  - **q even** (H = 0): u_q = `00100` and the `01` after it form the half digit `0010001`, so r' = q/2 = r and H' = 1. That `01` is also x' = 1.

  - Either way 2r' + H' = q + 1, H' = 1 − H, and the emission is e = (r'+H') − (r+H) = 1 − H.

- **S** (μ = E, so μ_1 = F): RC' = u_1 ... u_q w*, with first tokens `00` at odd i and `01` at even i.

  - By the class rule below, S needs y = H = 1. So q = 2r + 1 is odd, σ = μ_q = F, and the UF on u_q has set the first token of w* to `01`.

So x' = 1 again.

  - The pairs (u_1 u_2), ..., (u_(q−2) u_(q−1)) are d(0) Z.

  - u_q and the `01` after it form the half digit, and that `01` is x' = 1.

  - So r' = r, H' = 1 = H, and e = 0.

- In both cases RC' is `U^(2r'+H') W(f', e)` except that every R digit has bit 0 (its bit token is `00`, not `01`). By the next overflow the counter has counted these bits up to 1 again, which is the form X needs.

The end unit was never read, so e and m are unchanged.

**Class rule.** N ⇔ μ = F ⇔ σ flipped 2r + y times is F. For y = 0 the tail returns in F (§4.2, first 0 at y), so the class is N.

For y = 1, N ⇔ σ = E. This is the class column of §4.2's table, and it does not depend on r.

**L\* closure and the front unit.**

- Class N: x' = 1 and y' = 1 − y = H' (§4.2's table).

- Class S: x' = 1 and y' = y = H = H'.

So the new tail is in L\*, and (y, z) → (y', z') is the TAILFRONT arrow, with emission e = 1 − y for N and e = 0 for S. All of this holds for every r ≥ 0, every a and G, and both normal and pause context, because the tail's return never reads left of the tail, and RB, BN and the S return are parametric.

In the .v the three overflow outcomes are `OvN1` (H = 1, the tail returns in E, N, H' = 0), `OvN0` (H = 0, the tail returns in F, N, H' = 1 and one more R digit) and `OvS1` (H = 1, the tail returns in F, S), each for an arbitrary left context.

### 4.4 ENDCARRY (f = 1^15)
After CF1, C reads the end unit `(0e_1)...(0e_m) 01`. Let j = the number of leading 1s of e, with j := m + 1 when all m bits are 1. In that case the end marker `01` counts as one more 1, the first blank `00` after it is the first 0, R7 writes a new marker there, and m grows by 1.

R6^j and R7 run, and then the transducer of §4.2 returns over the j processed `10` tokens: alternately L3 (E→F, gives `00`) and L3F (F→E, gives `01`), the rightmost first, in mode E.

So token i of the end unit (1 ≤ i ≤ j) becomes `00` if j − i is even and `01` if j − i is odd, and the mode on the last cell of P1 is E for even j and F for odd j (`retf_PP`, `retf_PPP`).

- **j even:** PEN `P1 <E → <E F(100100010001010)`. Then lemma RB with σ = E and w = F(100100010001010)·(end unit), q = 2r + 1 (H = y = 1), so μ = F and the result is **N**.

The end bits become `(10)^(j/2) 1 rest`, f' = 100100010001010, H' = 0, e0.

- **j odd:** PFN `P1 <F → <F F(010000100100101)`, which never reads the end unit, so its first token stays `00` (e'_1 = 0).

Then RB with σ = F: w = F(010000100100101)·(end unit) starts with `00`, as RB needs. q = 2r + 1 is odd, so μ = E and the result is **S**.

The UF on u_q sets the first token to `01`, so f' = 110000100100101 and H' = H = 1, e0. The end bits become `(01)^((j+1)/2) rest`.

- Both f' give the TAILFRONT arrows from front 11: 11 →N,e0→ 00 and 11 →S→ 10. So ENDCARRY also closes L\* and follows TAILFRONT.

In the .v this is `Tail11_end`: `e_split` gives e = 1^j 0 e' or e = 1^m, and the parity of j picks the case. PEN and PFN are the two fixed transducer runs `F1E_ret` and `F1F_ret`.

### 4.5 TAILFRONT and closure of L\*
For every tail in L\* and every r, a, G, in normal or pause context, the overflow is N or S with exactly the forms above. The new tail is again in L\*, with m' = m except in the ENDCARRY growth case.

The front unit and the emission follow:

```
TAILFRONT:   10 -N,e0-> 01 -N,e1-> 11 -N,e0-> 00 -N,e1-> 10,     11 -S,e0-> 10
```

S occurs only from front unit 11.

- **Proof:** §4.2 (the first-zero cases), lemma RB with the boundary analysis (§4.3), and ENDCARRY (§4.4). Every statement over r, a, G and the context is parametric.

The only computations are 16 fixed transducer runs: 14 first-zero cases, plus PEN and PFN.

## 5. Macro dynamics and the invariant

### 5.1 Quantities at a configuration X(a; G; r, H; f, e)

- R := r + H, N = k + 1 + R, M = 2^N;

- Γ := Σ_(i=1..k) (g_i − 1)·2^(i−1);

- c := 2^(k+R) − 2^(k+1) − 2Γ − 4;

- s := a − c, κ := c − M/4.

### 5.2 One overflow and its pause, in closed form
**Slot rule.** In a pause the wall is `(100)^w 1` and each P100 cycle lowers w by 1 and adds 2 to v. Let the next overflow slot be cyc = (2^N − 2 − v)/2 cycles away.

- If **cyc ≤ w − 1**, the slot is reached with wall `(100)^(w−cyc) 1`, where w − cyc ≥ 1, and value 2^N − 2. This is a PO slot: PO, or SILENTP, both need n ≥ 1.

- If **cyc ≥ w + 1**, after w cycles the wall is the bare `1` and v + 2 < 2^N, so WX ends the pause.

- If **cyc = w**, the slot would be reached with the bare wall `1`. No rule covers this: PO and SILENTP need n ≥ 1, and WX needs v + 2 < 2^N.

INV keeps every path away from it (§5.3).

**After NO with emission e:** R' = R + e and M' = 2^e·M.

- The first ZX (p = 0) creates the gap-2 digit. The zones are then rebuilt innermost first: for each zone, (g − 2) P010 cycles, then ZX (ZXN for the last one).

Every gap is restored exactly.

- After ZXN the counter value is v_0 = 2^(k+2) + 4Γ, the wall is `(100)^(a−2) 1` and the lead is 0.

- The pause then runs P100 cycles (+2 each). The next overflow slot comes after c' = (M' − 2 − v_0)/2 cycles; for e = 0 this is c' = c + 3.

- By the slot rule with w = a − 2: if c' ≤ a − 3, the slot is a PO slot with p = c' and wall a − 2 − c' ≥ 1. If c' ≥ a − 1, WX ends the pause and Inc runs to the next normal-mode overflow.

c' = a − 2 never occurs under INV.

**After PO at inner lead p with emission e:** the gap-2 digit and the zones of G are rebuilt as above. Then the zone Zn(p) is rebuilt: (p − 2) P010 cycles, then ZXP1 and ZXP2, which inserts the new gap p − 1. The wall drops by 3 (ZXP1 by 1, ZXP2 by 2).

The value is 2(v_G + 2(p−2) + 2) + 2.

**The four paths** between consecutive normal-mode overflows, starting from front unit f. Each is a composition of the rules above (algebra below, all in terms of M and s):

| path | from f | outcomes | M' | s' | κ' | f' |
|---|---|---|---|---|---|---|
| S | 11 | S | M | s + M | κ | 10 |
| P1 | 10 or 11 | NO e0, PO e1, WX | 4M | M + 10 − s | 2 | 11 or 10 |
| P1S | 10 | NO e0, PO e1, SILENTP, WX | 4M | 5M + 10 − s | 2 | 10 |
| P3 | 10 | NO e0, PO e1, PO e0, PO e1, WX | 32M | 9M + 32 − s | 8 | 10 |

The algebra:

- **S:** SILENT gives lead a + 1 and counter 0. Then M − 1 Incs reach the next overflow at a + M, with G and R unchanged.

- **NO e0:** p = c + 3, so PO#1 has wall s − 5 and inner lead p = c + 3.

- **PO#1 (e1):** G'' = (c+2) ∪ G, R'' = R + 1, M'' = 4M. Using 2p = M − 2^(k+2) − 4Γ − 2, the value after ZXP2 is v_1 = 2M − 6. The wall is s − 8 and the lead 0.

  - The next slot comes after (4M − 2 − v_1)/2 = M + 2 cycles.

  - **If M + 2 ≥ (s − 8) + 1, i.e. s ≤ M + 9:** WX gives lead s − 7 and value v_1 + 2(s − 7). The next overflow is at a'' = 2M + 12 − s.

With the new gaps, c'' = M + 2 (so κ'' = 2) and s'' = M + 10 − s. **This is P1.**

  - **If M + 2 ≤ (s − 8) − 1, i.e. s ≥ M + 11:** PO#2 is reached at p = M + 2 with wall s − M − 10 ≥ 1. Its front unit is 11.

  - s = M + 10 is the excluded case cyc = w. INV gives s ≤ M − 14 or s ≥ M + 24, so it never occurs.

    - **S at PO#2 (SILENTP):** p = M + 3, wall s − M − 11, value 0. The next slot is 2M − 1 ≥ (s − M − 11) + 1 cycles away (s ≤ 3M + 9), so WX gives lead s − 7 and value 2(s − M − 10).

Then a'' = 6M + 12 − s and s'' = 5M + 10 − s. **This is P1S.**

    - **e0 at PO#2:** gap M + 1 is inserted, M''' = 8M, value 8M − 18, wall s − M − 13. The next slot is 8 ≤ (s − M − 13) − 1 cycles away (s ≥ M + 22): PO#3 at p = 8 with wall s − M − 21. Its front unit is 00, so the outcome is e1.

    - **PO#3 (e1):** gap 7 is inserted, M4 = 32M, value 16M − 18, wall s − M − 24 ≥ 0. The next slot is 8M + 8 ≥ (s − M − 24) + 1 cycles away, so WX follows.

Then a'' = 17M + 40 − s, c'' = 8M + 8 (κ = 8) and s'' = 9M + 32 − s. **This is P3.**

### 5.3 The invariant
INV at a configuration X: **M ≥ 256** (N ≥ 8), κ ∈ {2, 8}, all gaps ≥ 7, tail in L\*, and

- f = 11 and 24 ≤ s ≤ M/4 + 2, **or**

- f = 10 and s ∈ [8, M − 14] ∪ [M + 24, 2M].

Notes on INV:

- **M ≥ 256 is preserved:** M' ∈ {M, 4M, 32M} on every path, and the initial configuration has M = 256.

- **It is needed:** the side conditions below use M ≥ 256 and c = M/4 + κ ≥ 66. Without it, INV as written would also admit N = 5 (k = 0, R = 4, κ = 2) and N = 7 configurations, where the argument does not apply.

- **It gives k ≥ 1.** From c = M/4 + κ, Γ = 2^(N−3) − 2^k − 2 − κ/2. k = 0 needs Γ = 0, which means N = 5. So under INV there is at least one large-gap digit, and the last zone of every NO rebuild is a ZXN preceded by a ZX.

**Which path runs** (front unit and s decide; at a 11 slot both choices are covered):

| front unit f | s | paths | why |
|---|---|---|---|
| 11 | [24, M/4+2] | S or P1 (the tail chooses) | 11 allows S or e0; after e0 the front unit is 00, which forces e1 at PO#1; then s ≤ M + 9, so WX |
| 10 | [8, M−14] | P1 | 10 forces e0, then 01 forces e1 at PO#1; s ≤ M + 9, so WX |
| 10 | [M+24, 2M] | P1S or P3 | after PO#1 the front unit is 11; s ≥ M + 11, so the PO#2 slot is reached; the tail chooses S (P1S) or e0 (P3) |

**Closure** (images of the interval end points; every map has slope ±1):

| path | image of s | target |
|---|---|---|
| S | [M+24, 5M/4+2] | inside [M+24, 2M], f = 10 |
| P1 from 11 | [3M/4+8, M−14] | inside [8, 4M−14] = [8, M'−14], f = 10 |
| P1 from 10 | [24, M+2] | exactly [24, M'/4+2], f = 11 |
| P1S | [3M+10, 4M−14] | inside [8, M'−14], f = 10 |
| P3 | [7M+32, 8M+8] | inside [8, M'−14] with M' = 32M, f = 10 |

**Side conditions** that keep every rule inside its domain. They are linear in s, so the interval end points suffice. Below, M ≥ 256 and c = M/4 + κ ≥ 66:

- **NO:** a = s + c ≥ 74 ≥ 2 (ZXN needs n ≥ 2).

- **PO#1 slot:** w = a − 2 and cyc = c + 3, so cyc ≤ w − 1 ⇔ s ≥ 6. PO#1 has p = c + 3 ≥ 69 and wall s − 5 ≥ 3 (ZXP1 n ≥ 3, ZXP2 n ≥ 2).

- **After PO#1:** w = s − 8 and cyc = M + 2. WX for f = 11 and for f = 10 with s ≤ M − 14, since s ≤ M + 9. PO#2 for s ≥ M + 24, since s ≥ M + 11.

- **PO#2:** p = M + 2 and wall s − M − 10 ≥ 14.

- **SILENTP at PO#2:** wall s − M − 10 ≥ 14 ≥ 1. Afterwards WX, since 2M − 1 ≥ s − M − 10.

- **PO#3 slot:** w = s − M − 13 and cyc = 8 ≤ w − 1. PO#3 has p = 8 and wall s − M − 21 ≥ 3. Afterwards WX, since 8M + 8 ≥ s − M − 23.

- **New gaps:** c + 2 ≥ 68, M + 1 and 7 are all ≥ 7. So every ZX zone has g + 1 ≥ 8 ≥ 3 blocks, and every PO has p ≥ 8, so its zone Zn(p) is rebuilt by p − 2 ≥ 6 P010 cycles, then ZXP1 and ZXP2.

- **The rebuild never overflows.** Let the slack be (2^N − 2 − v)/2, the number of +2 cycles left before the next slot.

  - A zone of gap g (g − 2 P010 cycles, then a ZX or ZXN that inserts gap g; the first ZX at lead 0 is the case g = 2) needs slack ≥ g − 1 before it.

It leaves slack' = 2(slack − g + 2) − 1, since the ZX adds 2 and then doubles the value with one more digit.

  - The PO zone Zn(p) (p − 2 P010 cycles, ZXP1, then ZXP2, which adds 1 and doubles) needs slack ≥ p before it and leaves slack' = 2(slack − p + 1).

  - Inverting: slack before = (slack' + 2g − 3)/2 ≥ g − 1 ⇔ slack' ≥ 1, and slack before = slack'/2 + p − 1 ≥ p ⇔ slack' ≥ 2.

  - At the end of every rebuild the slack is the distance to the next slot: c + 3, M + 2, 8 or 8M + 8, all ≥ 8. Going backwards, every zone had enough slack.

So no carry reaches the tail during a rebuild.

- **S inside a pause happens only at PO#2.** PO#1 and PO#3 have front unit 01 or 00. After SILENTP the pause ends with WX before another slot (above).

**In the .v.** `INV a G r1 St` is this invariant at the configuration `KX a G r1 St`. At a normal-mode overflow the front unit is 11 or 10, so H = y = 1, and the R block is r1 = r gap-1 digits plus the half digit.

With Q := 2^(|G| + r1) = M/4 and gval G := Σ_i 2^i g_i, INV says:

- all gaps are ≥ 2 (this is all the rules need; the run has gaps ≥ 7), and Q ≥ 64;

- κ ∈ {2, 8}, with gval G + 6 + κ = Q (this is c = M/4 + κ), and a = s + Q + κ;

- the tail St is in L\* with front 11 and 24 ≤ s ≤ Q + 2, or with front 10 and s ∈ [8, 4Q − 14] ∪ [4Q + 24, 8Q].

The paths are `pathS` (a ≥ 1), `pathP1` (s ∈ [8, M + 9]), `pathP1S` (s ∈ [M + 11, 3M + 9]) and `pathP3` (s ∈ [M + 24, 9M + 31]).

`pre1` is the part shared by the last three (NO e0, the pause, PO#1 e1). Each path takes the tail's behaviour at each overflow as a hypothesis (`OvNp`, `OvSp`), and `step` supplies it from §4.2's lemmas.

The rebuild's no-overflow condition is stated only on the final value (`Zones`); `zv_ge` (2^|L|·v ≤ zv L v) carries it back to every earlier zone.

This is the slack argument above in one line. `step` checks the image intervals with `lia`.

## 6. Initial segment
The first configuration in X ∩ INV is reached by direct simulation from the blank tape in **92,299 steps**:

`0^inf A>(001)^121 00 0110001 Z^28 0110001 Z^2 (0110001100)^5 01100 W(111111011110101, 010)`

So a = 121, G = (28,), r = 5, H = 1, R = 6, N = 8, M = 256. The tail is in L\* with m = 3, x = 1, H = y = 1, and the front unit is 11. Further c = 66, s = 55 ∈ [24, 66] and κ = 2. In the .v: `init : c0 -->* KX 121 [28] 5 St0` (one `solve_init`) and `INV0`.

Earlier all-ones normal-mode records exist (steps 230 … 17,206). Some are X-configurations outside INV, for example step 5,786 with G = () and s = 3. The proof does not use them: the initial segment is the exact 92,299-step run.

## 7. Conclusion

- **Coverage.** Every member of the invariant set takes one of the paths S, P1, P1S, P3, whatever the tail chooses at each `11` slot.

Each path is a finite composition of rules (Inc, SILENT, NO, PO, SILENTP, P100, WX, P010, ZX, ZXN, ZXP1, ZXP2), each applied inside its domain (§5.3).

Each path lands in the invariant set again (`step`).

- **Progress.** Each path contains an overflow, and every overflow starts with R2, so each path takes at least one step (`-->+`).

`progress_nonhalt_cond` with `P := INV`, after `multistep_nonhalt` with `init`, gives `nonhalt`.

- **Halting.** Nothing more is needed: every rule is a derivation in busycoq's step relation, and a halting configuration has no successor.

(Informally: the only halting transition is B reading 1, B is entered only from A0 `1RB` and F1 `1LB`, and in every window run above, the B that follows reads 0.)

## 8. Mapping to busycoq

### The template, TM1
`CounterClass3v2.v`, `Module TM1` proves a multi-level counter by hand: sweep lemmas, an induction on the carry depth (`E_stmt`, `E_all`), `Climb`/`Climbs`, macro lemmas `Mac_*`, then a trajectory family `Traj n` proved by strong induction, and `nonhalt` by `progress_nonhalt_simple`.

- **Kept:** window lemmas by `es`, shift rules by `shift_rule_R`/`shift_rule_L`, a carry lemma by induction on the carry depth (`IncC`, as `E_stmt`/`E_all`), macro lemmas chained with `follow`, and `multistep_nonhalt` from an exact initial segment.

- **Changed:** the counter is a list of gaps read in tokens (`ctr gs v`), not TM1's unary blocks. The closing argument is not a strong induction over a trajectory family.

It is an invariant on macro states `(a, G, r1, tail)` with `progress_nonhalt_cond`, because the tail's choices at front 11 make the orbit non-uniform.

- **New:** the token layer; the return transducer `retf` with `retf_spec`, which handles the overflow, the R block and the tail without a 16,384-entry table;

one IR shape `KP` for normal and pause mode, so each pause rule is one generic lemma; the tail's behaviour as a hypothesis of the path lemmas (`OvNp`, `OvSp`);

and the zone-rebuild induction `Zones` with its side condition on the final value only.

The .v is 1,327 lines, against 986 for the template file. It imports `Individual62` from busycoq and the stdlib `Lia`, `String`, `List`, `Arith`.

Every lemma is top level (no Section, no Module, no Hypothesis).

### How the .v file is organized

| this write-up | lemma(s) in the .v |
|---|---|
| §1 tokens | `tok` (`T0` = `00`, `T1` = `01`, `TZ` = `100`), `ptok` (`P` = `10`, `PZ` = `010`), `tw`, `pl`, `prc` (processing), `noT0` |
| §1 counter | `ctr gs v` (gaps LSB first, last digit = its bit only), `dig`, `LD`, `ctr_zero`, `ctr_ones`, `gsof G r1` (= G, then 2, then r1 ones), `sfx H` |
| §1 tail | `tailw`/`tailx` (the 15 bits as booleans plus the end-unit list), `Lst y z` (L\* with front unit (y, z)) |
| §1.3 families | `KP W p gs v H St` (an IR; W = 0^inf is normal mode), `KX a G r1 St` (the configuration X) |
| §2.1 window lemmas | `AT0`, `CT1`, `CTZ`, `CT0`, `EPZ`, `EP`, `FP`, `FPZP`, `ENDl`, `B1`, `BN`, `ENDZX` (each `es`); `CTZs`, `EPZs`; `Csweep`; `Bnc` |
| §2.2–2.3 | `IncC`, `IncL`, `Inc`, `Inc1`, `Incs` |
| §3 | `TwoInc`, `ZXg`, `ZXP2g`; `P100`, `P100s`, `WX`, `P010s`, `Zone`, `Zones`, `zv_ge`, `ZXN`, `ZXP`; walls `zw`, `zv`, `zg`, `zp`, `gval`, `wallOv`, `wallPO` |
| §4.1 | `OvSweep` |
| §4.2 | `retf`, `retf_spec`, `retf_app`, `TailRet`, `Tail0z`, `Tail10`, `Tail11` |
| §4.3 | `RB_E2`, `RB_F2`, `RB_E1`, `RB_F1`, `BNp`, `retf_dig`, `retf_LD`, `retf_lead`; `OvN1`, `OvN0`, `OvS1` |
| §4.4 | `Tail11_end` (`e_split`, `retf_PP`, `retf_PPP`, `F1E_ret`, `F1F_ret`) |
| §4.3, §5.2 rules | `OvNp`, `OvSp`, `OvNp1`, `OvNp0`, `OvSp1`; `NOrb`, `POrb`, `SILENT`, `SILENTP` |
| §5.2 paths | `pathS`, `pre1`, `pathP1`, `pathP1S`, `pathP3` |
| §5.3 | `INV`, `step` |
| §6 | `St0`, `init`, `INV0` |
| §7 | `nonhalt`: `multistep_nonhalt` with `init`, then `progress_nonhalt_cond` with `P := INV` |

## 9. Numerical sanity checks

All by direct simulation of the transition table. They are evidence only; the result rests on the .v file alone.

- **Window lemmas.** All 23 rows of §2.1 run exactly as stated (full output word, exit side and state, steps) and never read outside their windows.

PEN and PFN were also run with each 2-cell right context, which stays unchanged.

- **Inc_L.** 11,472 exhaustive instances (N ≤ 4, all v, gaps 1..3, a ≤ 3, 6 left contexts) and 400 random ones (a and gaps up to 300, N ≤ 8, random L and T): exact tape, F on the last cell of L, L untouched, exact steps.

- **Pause rules.** All seven, on random and small instances (random walls, p ≤ 200, gaps ≤ 60, ≤ 6 digits): exact whole tape at the next IR, exact steps.

- **The tail.** All 16,384 settings of f with x = 1, by plain simulation of the 73-cell window: the first-zero rule of §4.2 holds, and the front-unit counts are 00 → 10: 4,096;

01 → 11: 4,096; 10 → 01: 4,096; 11 → 00 (N): 2,485; 11 → 10 (S): 1,610; f = 1^15: 1.

- **Whole overflows.** 65,536 (every f in normal context with r = 0 and r = 3, and in pause context with r = 0 and r = 2): the NO/PO/SILENT/SILENTP forms, the class rule, 2r' + H' as in lemma RB, L\* closure, the untouched end unit, and TAILFRONT all match.

ENDCARRY: every end unit with m ≤ 10 in both contexts (4,094 cases) and 300 random ones with m ≤ 40.

- **Initial segment.** From the blank tape to the configuration of §6 at step 92,299, exact.

- **Arithmetic.** The interval closure and every side condition of §5.3, exactly, for N = 8..400, both κ, all three intervals, with the three-way slot rule.

An exhaustive search over all front-unit sequences to depth 48 found no degenerate case.

- **Whole paths.** From configurations in INV, the real machine was run to the next normal-mode overflow and the result required to be in INV with exactly the predicted path, M', s', κ' and f'.

The coverage was N = 8 exhaustively (all G, both κ, every s of the three intervals: 4,599 starts), 172 random starts with N = 9..12 (end points, f = 1^15 and ENDCARRY at PO#2 included), 72 targeted ENDCARRY-at-PO#2 cases, and 6 continuous chains.

- **The real run.** No halt in 10^10 steps. The records at steps 92,299, 1,006,516, 14,514,329 and 114,113,163 are joined by the paths P1, P1 and S.

A macro model built from the rules reproduces every normal-mode entry from step 36,124 to step 555,048,797 exactly; the inserted gaps are 28, 68, 260, 1028, 4097 and 7.


AI assistance: the proofs and original write-ups were produced with the help of Claude (Anthropic), with independent review and submission preparation by GPT-6 Astra (OpenAI).
