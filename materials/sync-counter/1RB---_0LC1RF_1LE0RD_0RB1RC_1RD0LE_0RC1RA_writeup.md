# 1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA: never halts

This machine is a different blank-start orbit of the binary counter and moving-front system described in the [companion proof](1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---_writeup.md).

Its state names differ, but the same hexagonal invariant proves nonhalting.

The proof below defines the state map and verifies the new initial configuration. References to “parent §n” mean section n of that companion proof.

Both machines appear in dyuan01's October 1 longitudinal-filter list.

**Summary.** The tape is the parent's (the parent's summary): a binary counter on the left (digits `1010`/`0010`), a row of 5-cell blocks `A = 00111` and `B = 10111` to its right, and a head carrying `001` that bounces between the counter and the right edge, adding 1 to the counter on each bounce.

In the P phase each bounce appends a B block. Each counter overflow adds a digit and a front `111`, which walks right through the A blocks;

when it reaches the B blocks, they all become A blocks. At each cycle start S(k,Y,Z) the block counts follow a two-branch affine map, and both branches keep the hexagon R_N of parent §4.

Since this machine is the parent's table under a state renaming (Lemma R, §0), every rule of the parent's proof holds here with the head states renamed, and the cycle lemma and the invariant hold verbatim.

Relative to the parent:

1. **Rules, cases and invariant: unchanged.** No rule, case split or invariant clause changes; only head-state names do (§1).

2. **Initial segment: changed.** From the blank tape the machine reaches S(6,14,4) = Q(7,65,1,14,4) in 16,590 steps, where the parent reaches S(6,16,0) in 17,215 steps (§2).

3. **Base: in the same invariant.** (Y,Z) = (14,4) lies in R_64, on the facet 4Y+2Z ≥ N (64 = 64), the same facet the parent's base lies on (§2).

No clause of the invariant needs adjusting.

The two runs are different orbits of the same macro map, not the same orbit (§0, §4).

## 0. The map

| state here | 0 | 1 | = σ(parent state) | parent 0 | parent 1 |
|---|---|---|---|---|---|
| A | 1RB | **---** | σ(F) | 1RC | **---** |
| B | 0LC | 1RF | σ(C) | 0LD | 1RE |
| C | 1LE | 0RD | σ(D) | 1LA | 0RB |
| D | 0RB | 1RC | σ(B) | 0RC | 1RD |
| E | 1RD | 0LE | σ(A) | 1RB | 0LA |
| F | 0RC | 1RA | σ(E) | 0RD | 1RF |

Row σ(s) of this machine is the parent's row s with every target state t replaced by σ(t); symbols and directions are unchanged.

For example, the parent's C1 = 1RE becomes 1Rσ(E) = 1RF, which is B1 here. Among all 720 renamings of the six states, each with and without mirroring, σ is the only one that maps the parent's table to this one.

**Lemma R (relabelling).** For a configuration c, let σc be c with its head state renamed by σ; the tape and the head position stay the same.

Then c → c′ in the parent if and only if σc → σc′ in this machine, and c is halted exactly when σc is. So every parent run c →ⁿ c′ gives a run σc →ⁿ σc′ of this machine of the same length, and conversely.

*Proof.* The transition of state s on symbol b in the parent is (w, d, t) exactly when the transition of σ(s) on b here is (w, d, σ(t)), and the parent's cell s,b is undefined exactly when σ(s),b is undefined here.

∎

**Start.** This machine's c0 is `0^inf A> 0^inf` = σ(`0^inf F> 0^inf`).

- From F, the parent writes F0 = 1RC and is at `0^inf 1 C> 0^inf` after one step.

- From its own start A, the parent does A0 = 1RB, B0 = 0RC and is at `0^inf 1 0 C> 0^inf` after two steps.

These are different tapes, so this machine's run is σ of the parent's table run from `0^inf F> 0^inf`, which is a different orbit from the parent's own run.

**Halting cell.** The only undefined cell here is A1 = σ(F1). By Lemma R, parent §4 "Why F1 is never reached" becomes this:

- this machine enters A only by F1 = 1RA (= σ of the parent's E1 = 1RF), inside the shift rules FR3, FR4, FE1 and FE3 (parent §3.1);

- each time, A then reads a 0.

## 1. What carries over unchanged

| parent item | here | reason |
|---|---|---|
| parent §1 words and families: `C_k(n)`, A/B blocks, `P(k,n,X,z)`, `Q(k,n,x,y,z)` | the same words; the right-edge head state is B = σ(C), and the moving head is `<E 001` / `001 F>` (σ of `<A 001` / `001 E>`) | Lemma R |
| parent §3.1, the 21 shift rules | identical, with the head states renamed; same step counts | Lemma R; in the .v each is re-proved by `es` on this machine's table |
| parent §3.2 repeated rules (AL^a … D0R^t, CTR, OV, QC) and parent §3.3 macro rules R1, R2, R3, R4, R5, R5o (R4o as a remark) | identical, with the same step formulas and domains | Lemma R; the .v re-proves them on this table with the parent's proof scripts |
| parent §4 cycle states S(k,Y,Z), the cycle lemma with hypotheses (a)–(d), the hexagon R_N, (i)/(ii) and the parity remark | identical | the statements and proofs read only the rules and (k,Y,Z), never the start |
| parent §4 progress (every macro rule contains ENDL) | identical | Lemma R |
| **parent §5 initial segment** | **changed: §2** | different start |

The rules in busycoq comment style, for this machine:
```
1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA     (= sigma of 1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---, sigma = EDBCFA)

C_k(n): n in k bits MSB first, 1 -> 1010, 0 -> 0010;   A = 00111, B = 10111;  moving head <E 001 / 001 F>
P(k,n,X,z)   := 0^inf C_k(n) A^X B^z 00 B> 0^inf
Q(k,n,x,y,z) := 0^inf C_k(n) A^x 111 A^y B^z 00 B> 0^inf                    (x >= 1)

R1  P(k,n,X,z)      --> P(k,n+1,X,z+1)                     n+1 <= 2^k-1
R2  P(k,2^k-1,X,z)  --> Q(k+1,2^k+1,1,X-2,z+1)             X >= 2
R3  Q(k,n,x,y+2,z)  --> Q(k,n+3,x+2,y,z+1)                 n+3 <= 2^k-1
R4  Q(k,n,x,0,z)    --> P(k,n+z+2,x+z+1,0)                 n+z+2  <= 2^k-1
R5  Q(k,n,x,1,z)    --> P(k,n+2z+7,x+z+4,0)                n+2z+7 <= 2^k-1
R5o Q(k,n,x,1,z)    --> Q(k+1,2^k+1+3m,1+2m,x+z+2-2m,0)    m := n+2z+7-2^k >= 0,  x+z+2-2m >= 1,  3m <= 2^k-2
steps: R1 32X+32z+16t(n)+47,  R2 32X+32z+16k+61,  R3 96x+32y+32z+16(t(n)+t(n+1)+t(n+2))+197

cycle (N = 2^k):  S(k,Y,Z) := Q(k+1, N+1+3m, 1+2m, Y-2m, Z+m),  m = max(0,-Z)
  S(k,2j,Z)   -->+ S(k+1, 3j+Z,   N-3-4j-Z)
  S(k,2j+1,Z) -->+ S(k+1, 3j+3+Z, N-8-5j-2Z)
invariant (N >= 64):  8Y >= N, 8Y <= 3N, 3Z <= N, 8Z >= -N, 4Y+2Z >= N, 20Y+16Z <= 9N
start: c0 -->(16590) S(6,14,4) = Q(7,65,1,14,4)        [parent: c0 -->(17215) S(6,16,0)]
```

## 2. What changes: the initial segment (replaces parent §5)

A *canonical configuration* is a right-edge visit in state B that parses as P or Q. The table lists the canonical configurations of this machine's run from the blank tape, by direct simulation.

| step | configuration | how it is reached | parent step | parent configuration |
|---:|---|---|---:|---|
| 22 … 399 | P(1,1,0,0), P(2,2,0,0), P(2,3,0,1), P(3,5,1,0), P(3,7,1,2) | simulation; P(3,7,1,2) has X = 1, so R2 does not apply | 110 | P(2,3,1,0) |
| 1,711 | Q(5,20,3,1,0) | simulation (exact) | 1,507 | Q(5,17,1,2,2) |
| 3,047 | P(5,27,7,0) | R5 | 2,826 | P(5,25,7,0) (R3, R4) |
| 4,371 | P(5,31,7,4) | R1^4 | 4,996 | P(5,31,7,6) |
| 4,864 | Q(6,33,1,5,5) = S(5,5,5) | R2 | 5,553 | Q(6,33,1,5,7) = S(5,5,7) |
| 6,186 | Q(6,39,5,1,7) | R3^2 | 7,003 | Q(6,39,5,1,9) |
| 14,036 | P(6,60,16,0) | R5 (no overflow: 39+14+7 = 60 ≤ 63) | — | (parent: R5o with m = 0) |
| 15,825 | P(6,63,16,3) | R1^3 | — | |
| **16,590** | **S(6,14,4) = Q(7,65,1,14,4)** | R2 | 17,215 | S(6,16,0) = Q(7,65,1,16,0) |

The step numbers are direct-simulation values. From step 1,711 on they also equal the sums of the step counts of the rule chains of parent §3 (they agree exactly).

The argument needs only the first and last rows: the exact 16,590-step run from c0 and its end configuration. The induction starts at k = 6 (N = 64), as in the parent, because S(5,…) is below the N ≥ 64 bound of the invariant.

**The base, clause by clause.** The .v indexes cycle points by `CfgF k i y z := Q(k+2, 2^(k+1)+1+3i, 1+2i, y, z)`, the Q phase after i front steps;

in the coordinates of parent §4, N = 2^(k+1), Y = y+2i and Z = z−i. The base is `CfgF 5 0 14 4` = `Qc 7 (3·0 + (2^6+1)) (1+2·0) 14 4`, and `Inv 5 0 14 4` holds:

| `Inv` clause | value |
|---|---|
| 64 ≤ 2^6 | 64 ≤ 64 |
| 2^6 ≤ 8(y+2i) | 64 ≤ 112 |
| 8(y+2i) ≤ 3·2^6 | 112 ≤ 192 |
| 3z ≤ 2^6 + 3i | 12 ≤ 64 |
| 8i ≤ 8z + 2^6 | 0 ≤ 96 |
| 2^6 ≤ 4y + 6i + 2z | 64 ≤ 64 (**tight**) |
| 20y + 24i + 16z ≤ 9·2^6 | 344 ≤ 576 |

So in the coordinates (N, Y, Z) = (64, 14, 4), every facet of the hexagon holds, and 4Y+2Z ≥ N is tight (64 = 64). The parent's base S(6,16,0) is tight on the same facet.

The base sits on that facet: `Inv 5 0 13 4` and `Inv 5 0 14 3` are false (4y+2z = 60 and 62, both below 64).

The cycle-lemma hypotheses of parent §4 also hold at the base:

- (a) Y+2Z = 22 ≥ 1;

- (b) 3⌊Y/2⌋ = 21 ≤ 62;

- Y = 14 is even, so F(14,4) = (25, 29). Then (c) holds: 25 ≥ 0, 25+58 ≥ 1 and 36 ≤ 126;

- (d) Z′ = 29 ≥ 1.

All of these also follow from parent §4 (i), since the base is in R_64.

## 3. The argument (complete)

**Theorem.** `1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC1RA` does not halt from the blank tape.

1. **Initial segment.** This machine runs from c0 to σS(6,14,4) in exactly 16,590 steps without halting. This is a finite exact computation;

in Rocq it is one `esx` (`init0`).

2. **Base.** (Y,Z) = (14,4) is in R_64 (§2).

3. **Transfer.** Take the cycle lemma of parent §4 and the invariance of R_N under F_N (parent §4 (i)–(ii)). Together they say: for k ≥ 6 and (Y,Z) ∈ R_N, the parent goes S(k,Y,Z) →⁺ S(k+1,F_N(Y,Z)), and F_N(Y,Z) ∈ R_2N.

   - Their statements and proofs use only the rules of parent §2–§3 and arithmetic on (k,Y,Z).

   - By Lemma R, each parent run S →⁺ S′ is a run σS →⁺ σS′ of this machine of the same length.

   - So the same holds for this machine's configurations σS.

4. **Conclusion.** By induction from the base, this machine's run is an infinite chain of runs σS(k,·) →⁺ σS(k+1,·), each at least one step long.

So it never halts. This is the conclusion paragraph of parent §4 with "the run reaches S(6,16,0)" replaced by "the run reaches S(6,14,4)";

both points are in R_64. The run never reads A1: its first 16,590 steps are an exact computation, and every later step lies inside one of the shift rules of parent §3.1 (renamed), none of which reads A1 = σ(F1) (parent §4, "Why F1 is never reached").

∎

Nothing in the parent's argument depends on its own orbit except parent §5. The orbit data in parent §5 and §7 (the cycle states and rule counts of the parent's run) are evidence, not premises.

In the parent's .v this is visible directly:

- `cycle_step : Inv k i y z -> exists k' i' y' z', CfgF k i y z -->+ CfgF k' i' y' z' /\ Inv k' i' y' z'` does not mention the start.

- Only `init` (`c0 -->* CfgF 5 0 16 0`) and the last goal of `nonhalt` (`Inv 5 0 16 0`) do. This machine's .v replaces exactly those two (§5).

## 4. How this orbit relates to the parent's (explanation, not a premise)

There is no exact coupling between the two runs: they are different orbits of the same affine maps (spectral radius below 1).

Both stay in the hexagon, and their branch sequences differ:

| k | S(k,Y,Z) here, step | branch | parent S(k,Y,Z) | branch |
|---:|---|---|---|---|
| 6 | (14, 4), 16,590 | even | (16, 0) | even |
| 7 | (25, 29), 74,884 | odd | (24, 29) | even |
| 8 | (68, 2), 252,898 | even | (65, 48) | odd |
| 9 | (104, 115), 1,142,673 | even | (147, −8) | odd |
| 10 | (271, 186), 4,947,035 | odd | (214, 155) | even |
| 11 | (594, −31), 17,498,220 | even | (476, 438) | even |
| 12 | (860, 888), 72,729,902 | even | (1152, 655) | even |
| 13 | (2178, 1485), 314,863,727 | even | (2383, 1134) | odd |
| 14 | (4752, 2348), 1,268,929,120 | even | (4710, −39) | even |
| 15 | (9476, 4529), 5,039,089,135 | even | (7026, 7000) | even |

- **Rules used.** From the base to S(14,·), the run applies R1 5,046 times, R2 7, R3 2,025, R4 6, R5 1, R5o 1 and R4o never.

Its one R5o, Q(11,1430,271,1,321) → Q(12,2142,63,532,0) at step 17,498,220, has m = 1430+642+7−2048 = 31. That is the m ≥ 1 case of the R5o domain (parent §3.3), which the parent's own orbit also uses.

- **Size.** At 10⁹ steps this machine's tape spans 29,054 cells (−28..29,025); the parent's spans 23,607 (+23%). At 3·10⁹ steps it spans 47,451 cells with 18,841 nonzeros, and it has not halted.

## 5. The .v and how it differs from the parent's .v

The .v is the parent's .v (504 lines) with exactly these changes:

1. **The TM string**, in `TM_from_str` and in the comments.

2. **State names.** Every state name is renamed simultaneously by σ:

| Source | Target | Occurrences |
|---|---|---:|
| `{{A}}` | `{{E}}` | 37 |
| `{{C}}` | `{{B}}` | 6 |
| `{{E}}` | `{{F}}` | 35 |

The parent's .v names no other state. Every `es` proof closes unchanged, as Lemma R predicts.

3. **init.** `init0 : c0 -->* 0inf <* d1 <* d0^^5 <* d1 <* bA <* <[1;1;1] <* bA^^14 <* bB^^4 <* <[0;0] {{B}}> 0inf`, by `esx` (16,590 steps), and `init : c0 -->* CfgF 5 0 14 4`, by `apply init0` (conversion computes `ctr 7 65`).

4. **nonhalt.** The start index is `(5,0,14,4)%nat`. The final `unfold Inv. cbn. lia.` closes `Inv 5 0 14 4`; the tight clause is a `<=`.

5. **Everything else is the parent's text:** the counter, `QC`, and `Gad` with its lemmas.

This includes `Conv0`, `Conv1`, `Conv1o`, `Inv` and `cycle_step`.

The header comment and the closing rule-table comment are written for this machine, with the state letters renamed by σ and the new start line.

After the renaming, and outside comments, the .v differs from the parent's .v in four lines: the TM string, `init0`, `init` and the start index.

| item | lemma(s) in the .v |
|---|---|
| §1 shift rules and repeated rules | the 21 shift lemmas `ENDL` … `FE4` (each `es`) plus `D0R'` (D0R with `01` carried along); their repeated forms `ALs`, `BLs`, `ARs`, `BRs`, `D1Ls`, `D0R's`; the counter `ctr` with `CTR`, `OV`, `RT`, `OVRT`; and `QC`. All are stated for head states E/F (moving head) and B (right edge) |
| §1 macro rules R1–R3, R4, R5, R5o | `R1`, `R1s`, `R2`, `R3`, `Pfin`; one induction over `Gad` (`ConvNo`, `PostOV`, `ConvOV`) gives `Conv0` (R4), `Conv1` (R5) and `Conv1o` (R5o); all the parent's text |
| §2 base S(6,14,4) at step 16,590 | `init0` (one `esx`) and `init : c0 -->* CfgF 5 0 14 4` |
| §3 steps 2–4 | `Inv`, `cycle_step` (the parent's text) and `nonhalt` (`multistep_nonhalt` + `progress_nonhalt_cond` from index (5,0,14,4)) |

Lemma R is not a premise of the formal proof: every rule is re-proved on this machine's own table by `es`, and Lemma R explains why the parent's proofs re-close.

So the result rests on the .v alone; the prose here and in parent §3–§4 is the explanation. The proof is direct on the holdout string;

`verify/Eqv_v2.v` TM7 is not used.

## 6. Numerical sanity checks

These are independent of the Rocq proof and are evidence only.

- **Renaming.** σ = EDBCFA is the unique map, among the 720 state renamings each with and without mirroring, from the parent's table to this one.

The start is A = σ(F), and the only undefined cell is A1 = σ(F1).

- **Lockstep.** For 2·10⁶ steps, this machine's run from the blank tape equals σ of the parent's table run from `0^inf F> 0^inf`, at every step.

- **Shift rules (exact).** The 21 shift rules of parent §3.1, renamed, were executed on this machine's table: every step count is as in parent §3.1, A1 is never read, and all 11 defined transitions are used.

AL/BL/AR/BR^a were executed for a ≤ 12, CTR for all 502 (k,n) with k ≤ 9, and OV for k ≤ 9.

- **Macro rules (samples).** R1, R2, R3, R4, R5, R4o and R5o: 40 random instances each (k ≤ 10, block counts up to 200 or 2^(k−1)).

In each, direct simulation of this machine from the renamed start configuration gives the result and step count predicted by the rule chains of parent §3.

- **Initial segment (exact).** Direct simulation from the blank tape reaches σQ(7,65,1,14,4) at exactly step 16,590. It reaches Q(5,20,3,1,0) at step 1,711;

from there R5, R1^4, R2, R3^2, R5, R1^3, R2 lead to the base with step sum 14,879 = 16,590 − 1,711.

- **Canonical visits.** Every canonical right-edge visit from step 1,711 to 3·10⁷ is the one the rules predict from Q(5,20,3,1,0), in configuration and step: 857 of 857. The other 12 right-edge visits in state B in that range are the start and edge touches in the middle of a conversion.

- **Hexagon (exact).** The exact rational vertex check of parent §4 (ii) gives the same result: minimum slack 3/128, maximum 2u+v = 27/32.

- **Orbit.** Checked by direct simulation from the base to S(14,4752,2348) at step 1,268,929,120: the predicted cycle states (8 of 8) and every phase-boundary configuration (38) occur at the exact predicted steps, every cycle point is in R, and R4o is never used.

One level further, to S(15,9476,4529) at step 5,039,089,135: 9 of 9 cycle states and 43 boundaries.

AI assistance: the proofs and original write-ups were produced with the help of Claude (Anthropic), with independent review and submission preparation by GPT-6 Astra (OpenAI).
