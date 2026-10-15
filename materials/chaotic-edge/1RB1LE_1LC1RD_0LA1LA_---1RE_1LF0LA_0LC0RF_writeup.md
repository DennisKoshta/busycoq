# `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF` never halts

This machine is a known machine in disguise. Swap left and right, rename its states, and its table becomes the table of `1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF`, called the parent below. Only the start differs: this machine runs the parent's table from the parent's state C instead of A.

The parent is a bouncer that never halts. Its head runs back and forth between a fixed gadget at one end of the tape and the far end of the written part. Between them lie five long blocks of 1s, and their lengths follow exact macro rules, two of which alternate forever.

From the blank tape this machine falls into the parent's pattern after 4,098,826 steps. Then the parent's own opening moves apply in the same order, and they reach the start of the parent's endless cycle at step 153,013,640. From there the parent's proof applies unchanged.

## Machine and status

- **Machine:** `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF`, viewer https://bbchallenge.org/1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF
- **Holdout:** line 395 of the 698-machine BB(6) holdout list, spreadsheet class "Bouncer + Chaotic Edge".
- **Parent:** `1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF`, line 202 of the same list, proved non-halting in Coq. Its [full write-up](1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF_writeup.md) accompanies this one. Below, **P§n** means section n of that write-up.
- **Adjusted invariant:** none. Only the opening changes.
- **Status: fully formalized.** The accompanying .v (407 lines) proves `Lemma nonhalt: ~halts tm c0.` in Coq 8.20.1 against unmodified busycoq BB6. It imports `Individual62`, `ES_v3` and the Coq standard library.
  - `Print Assumptions nonhalt`: *Closed under the global context*.


### Template

The parent's .v is adapted from busycoq's `verify/TranslatedBellv5.v`, `Module TM1`:

- its macro rules are proved by ES_v3's `es'`;
- they are repeated by induction and chained with `follow`;
- it ends with `progress_nonhalt_simple`, as in `verify/Bouncer_v2.v`, `Module TM1`.

This file is the parent's .v with three changes:

- **Two tables.** `tm` is this machine and `tmP` is the parent's table. The parent's macro rules, `S_iter` and the double cycle `DC` are kept word for word, stated for `tmP`.
- **A new opening.** The parent's table is run from `C;; tape0` instead of `c0`. The direct run and the 20 macro steps get new arguments.
- **A conjugacy.** As in `verify/Skelet15.v`, a permutation lemma `perm : Perm (flip tm) tmP phi` links the two tables. busycoq's `flip_halts` (`Flip.v`) and `perm_halts` (`Permute.v`) then turn a halt of `tm` into a halt of `tmP` from C.

Skelet15 goes through `flip_halts_c0`; this file uses only the one-way lemma `flip_halts`. No new induction is needed.

### Where each section lives in the .v

The .v has four banner comments. *Macro rules (write-up 3.3, 3.4)* and *The double cycle (write-up 4)* cite the parent's write-up, P§3.3, P§3.4 and P§4. *Opening (write-up 2)* and *The relation (write-up 1)* cite this one.

| section | in the .v |
|---|---|
| §1.1, §1.2 mirror, renaming, Lemma M | `phi`, `perm`; busycoq's `flip_halts` and `perm_halts` inside `nonhalt` |
| §1.3 the family K | the parent's `G` and `Kr`, on half-length parameters (P§8.1) |
| §1.4 the parent's rules | `S_step`, `TE`, `TO`, `T6`, `T8`, `S_iter`, `DC`, all on `tmP` |
| §2.1 the direct part | `cc_steps`, `cc_steps'`, `rl`, `LR`, `Kr_list`, `Kr_cc`, `W1` … `W5`, `init1` … `init6`, `init` |
| §2.2 the macro steps | `opening` |
| §3, §4 the double cycle and the argument | `nonhaltP` (on `tmP`), then `nonhalt` |
| the table, σ and the rules, in busycoq's rule-table style | closing comment |

Section 6 describes the .v in more detail.

## Summary

The proof has four steps.

1. **Relation (§1).** Up to a mirror and a renaming of states, this machine's run from the blank tape is the parent's table run from `0^inf C> 0^inf`, step for step.
2. **Opening (§2).** That run reaches the parent's family K after 4,098,826 steps. The parent's 20 opening macro steps then take it to Even(12857, 212) at step 153,013,640.
3. **Domain (§3).** Even(12857, 212) is inside the domain of the parent's double cycle, which keeps it there.
4. **Conclusion (§4).** So the parent's double cycle repeats forever, and the machine never halts.

Section 5 is a remark on the table's third start. Section 7 lists the numerical checks.

## Notation

These are the parent's conventions (P§2).

- `l S> r` is state S reading the first cell of `r`, and `l <S r` is state S reading the last cell of `l`.
- Words are written left to right, `w^k` is k copies of w, and `0^inf` is the blank tail.
- `X --> Y` between configurations is an exact run of the machine.
- A *left record* is a step at which the head visits a cell left of every cell visited before. A *right record* is the same on the right.
- K(n,a,b,c,d) and Even(n, x) are the parent's families (P§2). The rules S, TE, TO, T6 and T8 are the parent's macro rules (P§1, P§3).

## 1. The relation

### 1.1 Mirror and renaming

Write σ for the map from the parent's states to this machine's states:

```
sigma (parent state -> this state):   A -> B,  B -> C,  C -> A,  D -> D,  E -> E,  F -> F
mirror:                               every move L becomes R and every R becomes L
```

Row σ(q) of this table is the parent's row q, with every direction reversed and every target state t replaced by σ(t). The written symbols are unchanged.

| this state | 0 | 1 | = σ(parent state) | parent 0 | parent 1 |
|---|---|---|---|---|---|
| A | 1RB | 1LE | σ(C) | 1LA | 1RE |
| B | 1LC | 1RD | σ(A) | 1RB | 1LD |
| C | 0LA | 1LA | σ(B) | 0RC | 1RC |
| D | --- | 1RE | σ(D) | --- | 1LE |
| E | 1LF | 0LA | σ(E) | 1RF | 0RC |
| F | 0LC | 0RF | σ(F) | 0RB | 0LF |

For example, the parent's A1 = 1LD becomes 1Rσ(D) = 1RD, which is this machine's B1. Among all 720 renamings, with and without the mirror, this is the only map from the parent's table to this one.

### 1.2 Lemma M

For a configuration c of the parent's table, let Φc be its mirror image with the head state renamed by σ:

- the cell at position p moves to position -p;
- the head moves with its cell, so a head at position h goes to -h;
- its state q becomes σ(q).

**Lemma M.** c → c′ in one step of the parent's table exactly when Φc → Φc′ in one step of this machine. And c is halted exactly when Φc is.

*Proof.* In c the head reads a symbol s in state q. Say the parent's cell (q, s) is "write w, move d, go to t".

In Φc the head reads the same s in state σ(q). This machine's cell (σ(q), s) is "write w, move the other way, go to σ(t)". So it writes w on the same cell, moves to the mirror of where the parent's head moves, and enters σ(t). That is Φc′.

D0 is the only undefined cell of both tables, and σ fixes D. So the halting configurations correspond too. ∎

By induction on the number of steps, an exact run of the parent's table of N steps maps to an exact run of this machine of N steps, and back.

### 1.3 The start, records and the family K

**Start.** This machine starts from `0^inf A> 0^inf`. Since σ(C) = A and the blank tape is its own mirror image, that is Φ of `0^inf C> 0^inf`. So this machine's run is Φ of the parent's table run from state C, step for step.

**Records.** Φ turns left records into right records. A round trip of this machine starts at its right end.

**The family K, mirrored.** In the parent's family K(n,a,b,c,d) (P§2) the head is in state F on the 0 just left of the 43-cell gadget G. The mirror images are

```
Phi K(n,a,b,c,d) = 0^inf 1^3 0 1^2 0^2 1^2 0 1^d 0^6 1^4 0 1^2 0 1^c 0^6 1^b 0 1^2 0 1^a 0 1^n 0^2 1^2 0 1^5 0 1^2 0^2 1^5 0 1^2 0 1^6 0 1^2 0 1^4 0 1^2 0^2 F> 0^inf
```

The 43 cells before `F>` are G read backwards. Since σ(F) = F, the head is again in state F, now on the blank cell just right of the reversed gadget.

### 1.4 The parent's rules carry over

Each rule of the parent is an exact run of the parent's table: the shift rules R1 and R2b, the macro rules S, TE, TO, T6 and T8 (P§1, P§3). By Lemma M the mirror of each is an exact run of this machine, with the same domain and the same step count.

In particular the double cycle (P§4) holds here in the form

```
Phi Even(n, x)  -->  Phi Even(n + 12x + 808, x + 32)        (n odd, x = 4 mod 8, x >= 52)
```

From here on, configurations are written in the parent's coordinates, as members K(...) of the parent's table run from C. On this machine they are read through Φ.

## 2. The opening run

### 2.1 The direct part

From `0^inf C> 0^inf`, the parent's table reaches

```
K(1953, 34, 68, 45, 18)
```

after exactly 4,098,826 steps. It is the first left record of that run whose configuration is in the family K.

Equivalently, this machine reaches Φ K(1953,34,68,45,18) at a right record after 4,098,826 steps from the blank tape, and no earlier right record has that shape. For comparison, the parent's own opening from A reaches K(1959,34,68,45,18) after 4,097,897 steps (P§5).

### 2.2 The macro steps

From there, the same 20 macro steps as in P§5 apply, in the same order. Each row applies its rule as many times as shown. The step numbers are the sums of the rules' step formulas.

The last column gives the parent's step at the same row, for comparison.

| after | rule | step | configuration | parent's step |
|---|---|---|---|---|
| opening | (direct run) | 4,098,826 | K(1953,34,68,45,18) | 4,097,897 |
| 1 | S^4 | 4,882,570 | K(2145,2,84,45,34) | 4,883,657 |
| 2 | TO | 7,706,738 | K(2733,38,96,35,18) | 7,713,999 |
| 3 | S^4 | 8,759,730 | K(2925,6,112,35,34) | 8,769,007 |
| 4 | T6 | 12,409,798 | K(3517,56,96,35,18) | 12,425,249 |
| 5 | S^6 | 14,417,014 | K(3805,8,120,35,42) | 14,435,489 |
| 6 | T8 | 18,605,120 | K(4345,46,86,89,18) | 18,629,265 |
| 7 | S^5 | 20,626,610 | K(4585,6,106,89,38) | 20,653,275 |
| 8 | T6 | 26,035,596 | K(5177,104,100,35,18) | 26,068,435 |
| 9 | S^12 | 31,916,508 | K(5753,8,148,35,66) | 31,955,395 |
| 10 | T8 | 37,990,554 | K(6293,74,86,113,18) | 38,035,111 |
| 11 | S^9 | 43,208,772 | K(6725,2,122,113,54) | 43,257,865 |
| 12 | TO | 50,868,554 | K(7313,144,116,35,18) | 50,923,821 |
| 13 | S^17 | 62,494,718 | K(8129,8,184,35,86) | 62,558,553 |
| 14 | T8 | 70,863,532 | K(8669,110,86,133,18) | 70,933,037 |
| 15 | S^13 | 81,154,982 | K(9293,6,138,133,70) | 81,231,039 |
| 16 | T6 | 91,512,408 | K(9885,180,132,35,18) | 91,594,639 |
| 17 | S^22 | 111,620,320 | K(10941,4,220,35,106) | 111,713,639 |
| 18 | TE | 122,940,170 | K(11497,134,82,157,18) | 123,039,285 |
| 19 | S^16 | 139,555,690 | K(12265,6,146,157,82) | 139,662,869 |
| 20 | T6 | 153,013,640 | K(12857,212,144,35,18) | 153,126,993 |

Each row's configuration was also confirmed by direct simulation of this machine at exactly that step, and by one unbroken run from the blank tape to step 153,013,640.

### 2.3 Every application is in its rule's domain

In every row, a, b, c and d are exactly the parent's values in P§5, and n is 6 smaller.

This is forced by the rules. In each of S, TE, TO, T6 and T8 the new a, b, c, d do not depend on n, and the new n is n plus a constant (P§1). So two runs that start with the same a, b, c, d keep them equal, and keep the same difference in n, as long as they apply the same rules.

The domains ask nothing of n except that it is odd. Here n starts at 1953 and changes by even constants, so it stays odd. The conditions on a, b, c, d are exactly the parent's, which P§5 checks row by row.

Only the step counts differ from the parent's, because every step formula has a term in n (for example 84n in S).

## 3. The double cycle's domain holds at the end of the opening

The last row is

```
K(12857, 212, 144, 35, 18) = Even(12857, 212)
```

since (212 + 76)/2 = 144. Here n = 12857 is odd, x = 212 = 4 (mod 8) and x ≥ 52.

These conditions are the whole domain of the double cycle, and the double cycle preserves them (P§4, closure). So no further invariant is needed.

The orbit from here is the parent's orbit from Even(12863, 212), with n smaller by 6 at every Even member. The reason is that the double cycle adds 12x + 808 to n, which does not depend on n.

## 4. The argument

**Theorem.** `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF` does not halt from the blank tape.

1. **Relation.** By Lemma M, this machine's run is Φ of the parent's table run from `0^inf C> 0^inf` (section 1.3).

2. **Direct part.** That run reaches K(1953,34,68,45,18) after 4,098,826 steps without halting (section 2.1).

3. **Macro steps.** The parent's rules S, TO, T6, T8 and TE take it to Even(12857, 212) at step 153,013,640. Each application is inside its rule's domain (section 2).

4. **Double cycle.** From there the parent's double cycle applies forever (section 3, P§4). Each round takes at least one step (P§6).

5. **Conclusion.** So the parent's table run from C is infinite. By Lemma M this machine's run is too, step for step. ∎

**The halting cell.** Here only B1 = 1RD enters D. So this machine halts exactly when B reads a 1 that has a 0 on its right.

B1 is σ of the parent's A1 = 1LD, and Lemma M maps halts to halts. Every step of the run above lies inside the direct part or inside one of the parent's exact rules, and none of those halts (P§7.1).

**Not a cryptid.** As for the parent (P§7.2), the top-level map (n, x) ↦ (n + 12x + 808, x + 32) is affine and all its parities are fixed.

## 5. Remark: the third start of the table

Line 599 of the 698 list, `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA`, is the same table started in the parent's state E, without the mirror. Its run reaches Even(13299, 220) at step 163,638,058, so the double cycle applies after its own opening. The accompanying [E-start proof](1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA_writeup.md) establishes that opening and its non-halting result.

This write-up and the .v prove only line 395.

## 6. The formalization

The .v proves `Lemma nonhalt: ~halts tm c0.` along the lines of section 4. It is the parent's .v with the following changes, and nothing else.

### 6.1 Two tables

`tm` is this machine and `tmP` is the parent's table. The parent's development is kept word for word, with its table renamed `tmP`. That part holds:

- the gadget `G` and the family `Kr`;
- the macro rules `S_step`, `TE`, `TO`, `T6` and `T8`, one `es'` each;
- `S_iter` (S repeated by induction), `Ev` and the double cycle `DC`.

Its lemmas use the parent's half-length parameters (P§8.1):

```
Kr n a b c d  =  K(2n+1, 2a, 2b, 2c+1, 2d)          Ev N X  =  Even(2N+1, 8X+52)
```

### 6.2 The opening

`init : C;; tape0 -->* Kr 976 17 34 22 9` is the direct run of section 2.1, since Kr 976 17 34 22 9 = K(1953,34,68,45,18). It runs on busycoq's list configurations (`cconfig_step`), with the parent's nested step counter `cc_steps'` (P§8.4).

The run is cut at five left records of `tmP`, where the tape is short in run-length form (16 to 19 pairs). The first piece starts by writing `C;; tape0` as an empty list configuration in state C.

| piece | from | to | steps | ends at step |
|---|---|---|---|---|
| `init1` | `C;; tape0` | `LR W1` | 696,153 | 696,153 |
| `init2` | `LR W1` | `LR W2` | 701,948 | 1,398,101 |
| `init3` | `LR W2` | `LR W3` | 696,114 | 2,094,215 |
| `init4` | `LR W3` | `LR W4` | 700,790 | 2,795,005 |
| `init5` | `LR W4` | `LR W5` | 700,644 | 3,495,649 |
| `init6` | `LR W5` | `Kr 976 17 34 22 9` | 603,177 | 4,098,826 |

Then `opening` follows the 20 rows of section 2.2. Its lemma arguments are the parent's, with only the first parameter N smaller by 3 (n smaller by 6). It ends at Even(12857, 212):

```
opening : Kr 976 17 34 22 9 -->* Ev 6428 20
```

### 6.3 Non-halting for the parent's table from C

`nonhaltP : ~halts tmP (C;; tape0)` applies `multistep_nonhalt` with `init` and `opening`. Then it applies `progress_nonhalt_simple` from (6428, 20) with `DC` for each step, exactly as the parent does (P§8.5).

### 6.4 The relation

`phi` is σ⁻¹, from this machine's states to the parent's:

```
phi:   A -> C,   B -> A,   C -> B,   D -> D,   E -> E,   F -> F
```

`flip tm` is this table with every move reversed (busycoq's `Flip.v`). The lemma `perm : Perm (flip tm) tmP phi` maps each defined transition as follows:

```
(flip tm)(q, s) = (w, d, t)  ->  tmP(phi q, s) = (w, d, phi t).
```

Undefined entries correspond too. The lemma holds by case analysis on the 12 cells.

`nonhalt` then chains two busycoq lemmas:

```
halts tm c0   ->   halts (flip tm) (A;; tape0)   ->   halts tmP (C;; tape0)
```

The first arrow is `flip_halts`, since the blank tape is its own mirror image. The second is `perm_halts`, since phi A = C. Then `nonhaltP` gives the contradiction.

## 7. Numerical checks

They are evidence only; the result rests on the .v file alone.

- **Relation.** σ with the mirror is the only map among the 720 renamings, with and without the mirror, and it matches all 12 cells. This machine and the parent's table from C run in lockstep, step for step, for 2 × 10⁶ steps, and their tapes are mirror images after 153,013,640 steps.
- **The family K.** The Φ K word of section 1.3 is the parent's K word reversed, for random parameter values.
- **Opening.** Both runs reach their K configuration after 4,098,826 steps, with no earlier K-shaped record. Every row of section 2.2 was confirmed by direct simulation of this machine, and by one unbroken run to step 153,013,640. Two independent simulators agree on both end points.
- **Domains.** Every application in section 2.2 is inside its rule's domain, and every row has the parent's a, b, c, d with n smaller by 6.
- **Double cycle.** Whole double cycles of this machine from Φ Even(n, x), for every x = 4 (mod 8) from 52 to 252, give the exact configuration and step count of P§4.
- **Orbit.** From step 153,013,640 to 10¹⁰ steps, every Even member and every Odd member (the configuration after TE, P§4) was found by direct simulation of this machine. Each has the a, b, c, d of a run start in the parent's own run, with n smaller by 6.
- **Halting.** No halt in the first 153,013,640 steps.
- **Remark.** Direct simulation of the run of section 5 reaches Even(13299, 220) at step 163,638,058.

AI assistance: Claude (Anthropic) assisted with the original formal proofs, proof sketches, scripts and checks. GPT-6 Astra (OpenAI) assisted with independent audit and submission preparation.
