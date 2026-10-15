# `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA` never halts

This machine is a known machine in disguise. Rename its states and its table becomes the table of `1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF`, called the parent below. No mirror is needed. Only the start differs: this machine runs the parent's table from the parent's state E instead of A.

The parent is a bouncer that never halts. Its head runs back and forth between a fixed gadget at one end of the tape and the far end of the written part. Between them lie five long blocks of 1s, and their lengths follow exact macro rules, two of which alternate forever.

From the blank tape this machine falls into the parent's pattern after 6,950,830 steps. Then 18 of the parent's macro moves, in an order of their own, reach the start of the parent's endless cycle at step 163,638,058. From there the parent's proof applies unchanged.

## Machine and status

- **Machine:** `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA`, viewer https://bbchallenge.org/1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA
- **Holdout:** line 599 of the 698-machine BB(6) holdout list, spreadsheet class "Bouncer + Chaotic Edge".
- **Parent:** `1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF`, line 202 of the same list, proved non-halting in Coq. Its [full write-up](1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF_writeup.md) accompanies this one. Below, **P§n** means section n of that write-up.
- **Adjusted invariant:** none. Only the opening changes.
- **Status: fully formalized.** The accompanying .v (458 lines) proves `Lemma nonhalt: ~halts tm c0.` in Coq 8.20.1 against unmodified busycoq BB6. It imports `Individual62`, `ES_v3` and the Coq standard library.
  - `Print Assumptions nonhalt`: *Closed under the global context*.


### Template

The parent's .v is adapted from busycoq's `verify/TranslatedBellv5.v`, `Module TM1`:

- its macro rules are proved by ES_v3's `es'`;
- they are repeated by induction and chained with `follow`;
- it ends with `progress_nonhalt_simple`, as in `verify/Bouncer_v2.v`, `Module TM1`.

This file is the parent's .v with three changes:

- **Two tables.** `tm` is this machine and `tmP` is the parent's table. The parent's macro rules, `S_iter` and the double cycle `DC` are kept word for word, stated for `tmP`.
- **A new opening.** The parent's table is run from `E;; tape0` instead of `c0`. The direct run is longer (ten pieces instead of six), and the 18 macro steps follow a chain of their own.
- **A renaming.** As in `verify/Skelet15.v`, a permutation lemma `perm : Perm tm tmP phi` links the two tables. busycoq's `perm_halts` (`Permute.v`) then turns a halt of `tm` into a halt of `tmP` from E.

There is no mirror, so busycoq's `Flip.v` is not used. No new induction is needed.

### Where each section lives in the .v

The .v has four banner comments. *Macro rules (write-up 3.3, 3.4)* and *The double cycle (write-up 4)* cite the parent's write-up, P§3.3, P§3.4 and P§4. *Opening (write-up 2)* and *The relation (write-up 1)* cite this one.

| section | in the .v |
|---|---|
| §1.1, §1.2 renaming, Lemma R | `phi`, `perm`; busycoq's `perm_halts` inside `nonhalt` |
| §1.3 the family K | the parent's `G` and `Kr`, on half-length parameters (P§8.1) |
| §1.4 the parent's rules | `S_step`, `TE`, `TO`, `T6`, `T8`, `S_iter`, `DC`, all on `tmP` |
| §2.1 the direct part | `cc_steps`, `cc_steps'`, `rl`, `LR`, `Kr_list`, `Kr_cc`, `W1` … `W9`, `init1` … `init10`, `init` |
| §2.2 the macro steps | `opening` |
| §3, §4 the double cycle and the argument | `nonhaltP` (on `tmP`), then `nonhalt` |
| the table, σ and the rules, in busycoq's rule-table style | closing comment |

Section 6 describes the .v in more detail.

## Summary

The proof has four steps.

1. **Relation (§1).** Up to a renaming of states, this machine's run from the blank tape is the parent's table run from `0^inf E> 0^inf`, step for step.
2. **Opening (§2).** That run reaches the parent's family K after 6,950,830 steps. Then 18 macro steps by the parent's rules take it to Even(13299, 220) at step 163,638,058.
3. **Domain (§3).** Even(13299, 220) is inside the domain of the parent's double cycle, which keeps it there.
4. **Conclusion (§4).** So the parent's double cycle repeats forever, and the machine never halts.

Section 5 is a remark on the table's other starts. Section 7 lists the numerical checks.

## Notation

These are the parent's conventions (P§2).

- `l S> r` is state S reading the first cell of `r`, and `l <S r` is state S reading the last cell of `l`.
- Words are written left to right, `w^k` is k copies of w, and `0^inf` is the blank tail.
- `X --> Y` between configurations is an exact run of the machine.
- A *left record* is a step at which the head visits a cell left of every cell visited before.
- K(n,a,b,c,d) and Even(n, x) are the parent's families (P§2). The rules S, TE, TO, T6 and T8 are the parent's macro rules (P§1, P§3).

## 1. The relation

### 1.1 The renaming

Write σ for the map from the parent's states to this machine's states:

```
sigma (parent state -> this state):   A -> E,  B -> C,  C -> D,  D -> F,  E -> A,  F -> B
```

Row σ(q) of this table is the parent's row q, with every target state t replaced by σ(t). The written symbols and the moves are unchanged.

| this state | 0 | 1 | = σ(parent state) | parent 0 | parent 1 |
|---|---|---|---|---|---|
| A | 1RB | 0RD | σ(E) | 1RF | 0RC |
| B | 0RC | 0LB | σ(F) | 0RB | 0LF |
| C | 0RD | 1RD | σ(B) | 0RC | 1RC |
| D | 1LE | 1RA | σ(C) | 1LA | 1RE |
| E | 1RC | 1LF | σ(A) | 1RB | 1LD |
| F | --- | 1LA | σ(D) | --- | 1LE |

For example, the parent's A1 = 1LD becomes 1Lσ(D) = 1LF, which is this machine's E1. Among all 720 renamings, with and without the mirror, this is the only map from the parent's table to this one.

### 1.2 Lemma R

For a configuration c of the parent's table, let σc be the same tape and head position, with the head state q replaced by σ(q).

**Lemma R.** c → c′ in one step of the parent's table exactly when σc → σc′ in one step of this machine. And c is halted exactly when σc is.

*Proof.* In c the head reads a symbol s in state q. Say the parent's cell (q, s) is "write w, move d, go to t".

In σc the head reads the same s in state σ(q). This machine's cell (σ(q), s) is "write w, move d, go to σ(t)". So the result is σc′.

D0 is the only undefined cell of the parent's table, and F0 = σ(D)0 is the only undefined cell of this one. So the halting configurations correspond too. ∎

By induction on the number of steps, an exact run of the parent's table of N steps maps to an exact run of this machine of N steps, and back.

### 1.3 The start and the family K

**Start.** This machine starts from `0^inf A> 0^inf`. Since σ(E) = A, that is σ of `0^inf E> 0^inf`. So this machine's run is σ of the parent's table run from state E, step for step, on the same tape.

**The family K.** The parent's family (P§2) is

```
K(n,a,b,c,d) = 0^inf <F G 1^n 0 1^a 0110 1^b 0^6 1^c 0110 1111 0^6 1^d 0110 0110 111 0^inf
```

where G is the parent's 43-cell gadget. The head is in state F on the 0 just left of G.

On this machine σK(n,a,b,c,d) is the same tape, with the head in state σ(F) = B. There is no mirror, so left records stay left records, and every configuration K(...) below is reached at a left record.

### 1.4 The parent's rules carry over

Each rule of the parent is an exact run of the parent's table: the shift rules R1 and R2b, the macro rules S, TE, TO, T6 and T8 (P§1, P§3). By Lemma R each is an exact run of this machine too, with the same domain and the same step count.

In particular the double cycle (P§4) holds here in the form

```
sigma Even(n, x)  -->  sigma Even(n + 12x + 808, x + 32)        (n odd, x = 4 mod 8, x >= 52)
```

From here on, configurations are written in the parent's coordinates, as members K(...) of the parent's table run from E. On this machine they are read through σ.

## 2. The opening run

### 2.1 The direct part

From `0^inf E> 0^inf`, the parent's table reaches

```
K(2583, 70, 76, 43, 18)
```

after exactly 6,950,830 steps. It is the first left record of that run whose configuration is in the family K, in any state.

Equivalently, this machine reaches σK(2583,70,76,43,18), in state B, after 6,950,830 steps from the blank tape, and no earlier left record has that shape. For comparison, the parent's own opening from A reaches K(1959,34,68,45,18) after 4,097,897 steps (P§5).

### 2.2 The macro steps

From there, 18 macro steps by the parent's rules reach the Even family. Each row applies its rule as many times as shown. The step numbers are the sums of the rules' step formulas.

| after | rule | step | configuration |
|---|---|---|---|
| opening | (direct run) | 6,950,830 | K(2583,70,76,43,18) |
| 1 | S^8 | 9,032,398 | K(2967,6,108,43,50) |
| 2 | T6 | 12,743,660 | K(3559,60,112,35,18) |
| 3 | S^7 | 15,134,804 | K(3895,4,140,35,46) |
| 4 | TE | 19,523,338 | K(4451,54,82,97,18) |
| 5 | S^6 | 22,019,854 | K(4739,6,106,97,42) |
| 6 | T6 | 27,598,730 | K(5331,112,104,35,18) |
| 7 | S^13 | 34,176,106 | K(5955,8,156,35,70) |
| 8 | T8 | 40,451,682 | K(6495,82,86,117,18) |
| 9 | S^10 | 46,448,502 | K(6975,2,126,117,58) |
| 10 | TO | 54,377,014 | K(7563,152,120,35,18) |
| 11 | S^18 | 67,117,990 | K(8427,8,192,35,90) |
| 12 | T8 | 75,779,054 | K(8967,118,86,137,18) |
| 13 | S^14 | 87,253,370 | K(9639,6,142,137,74) |
| 14 | T6 | 97,978,338 | K(10231,188,136,35,18) |
| 15 | S^23 | 119,736,338 | K(11335,4,228,35,110) |
| 16 | TE | 131,447,656 | K(11891,142,82,161,18) |
| 17 | S^17 | 149,713,782 | K(12707,6,150,161,86) |
| 18 | T6 | 163,638,058 | K(13299,220,148,35,18) |

The chain is

```
S^8 T6 S^7 TE S^6 T6 S^13 T8 S^10 TO S^18 T8 S^14 T6 S^23 TE S^17 T6
```

It is not the parent's chain. This run starts with other values of a, b, c and d, so its collisions come in a different order.

Each row's configuration was also confirmed by direct simulation of this machine at exactly that step, and by one unbroken run from the blank tape to step 163,638,058. In that run, these 126 configurations (the start, and the result of every single application of a rule) are exactly the K-shaped left records up to step 163,638,058.

### 2.3 Every application is in its rule's domain

The domains are those of P§1:

| rule | a | b | c | d |
|---|---|---|---|---|
| S | even, ≥ 10 | even, ≥ 6 | odd, ≥ 7 | even, ≥ 2 |
| TE | 4 | even, ≥ 88 | 35 | even, ≥ 20 |
| TO | 2 | even, ≥ 82 | odd, ≥ 37 | even, ≥ 18 |
| T6 | 6 | even, ≥ 82 | odd, ≥ 35 | even, ≥ 18 |
| T8 | 8 | even, ≥ 88 | 35 | even, ≥ 20 |

Every rule also needs n odd. Here n starts at 2583, and every rule adds an even constant to n (48, 556, 588, 592 or 540). So n stays odd.

**Parities.** In every row of section 2.2, a, b and d are even and c is odd. Within a block S^k, S adds 4 to b and d, subtracts 8 from a and keeps c, so the parities hold at every single application too.

**Bounds in a block S^k.** b and d only grow and c stays fixed, so the first application has the smallest b, c and d. a falls by 8 each time, so the last application has the smallest a.

The table below lists, for each row, the configuration the rule is applied to, the values of a over the applications, and the first application's b, c and d.

| row | rule | applied to | a | b | c | d |
|---|---|---|---|---|---|---|
| 1 | S^8 | K(2583,70,76,43,18) | 70, …, 14 | 76 | 43 | 18 |
| 2 | T6 | K(2967,6,108,43,50) | 6 | 108 | 43 | 50 |
| 3 | S^7 | K(3559,60,112,35,18) | 60, …, 12 | 112 | 35 | 18 |
| 4 | TE | K(3895,4,140,35,46) | 4 | 140 | 35 | 46 |
| 5 | S^6 | K(4451,54,82,97,18) | 54, …, 14 | 82 | 97 | 18 |
| 6 | T6 | K(4739,6,106,97,42) | 6 | 106 | 97 | 42 |
| 7 | S^13 | K(5331,112,104,35,18) | 112, …, 16 | 104 | 35 | 18 |
| 8 | T8 | K(5955,8,156,35,70) | 8 | 156 | 35 | 70 |
| 9 | S^10 | K(6495,82,86,117,18) | 82, …, 10 | 86 | 117 | 18 |
| 10 | TO | K(6975,2,126,117,58) | 2 | 126 | 117 | 58 |
| 11 | S^18 | K(7563,152,120,35,18) | 152, …, 16 | 120 | 35 | 18 |
| 12 | T8 | K(8427,8,192,35,90) | 8 | 192 | 35 | 90 |
| 13 | S^14 | K(8967,118,86,137,18) | 118, …, 14 | 86 | 137 | 18 |
| 14 | T6 | K(9639,6,142,137,74) | 6 | 142 | 137 | 74 |
| 15 | S^23 | K(10231,188,136,35,18) | 188, …, 12 | 136 | 35 | 18 |
| 16 | TE | K(11335,4,228,35,110) | 4 | 228 | 35 | 110 |
| 17 | S^17 | K(11891,142,82,161,18) | 142, …, 14 | 82 | 161 | 18 |
| 18 | T6 | K(12707,6,150,161,86) | 6 | 150 | 161 | 86 |

Every entry meets its rule's bounds:

- In the S rows the smallest a is 10 (row 9), the smallest b is 76, every c is at least 35 and every d is 18.
- The TE rows have c = 35, b ≥ 140 and d ≥ 46.
- The TO row has b = 126, c = 117 and d = 58.
- The T6 rows have b ≥ 106, c ≥ 43 and d ≥ 42.
- The T8 rows have c = 35, b ≥ 156 and d ≥ 70.

## 3. The double cycle's domain holds at the end of the opening

The last row is

```
K(13299, 220, 148, 35, 18) = Even(13299, 220)
```

since (220 + 76)/2 = 148. Here n = 13299 is odd, x = 220 = 4 (mod 8) and x ≥ 52.

These conditions are the whole domain of the double cycle, and the double cycle preserves them (P§4, closure). So no further invariant is needed.

The orbit from here is

```
Even(13299, 220) --> Even(16747, 252) --> Even(20579, 284) --> ...
```

with x = 220 + 32j. The parent's own orbit has x = 212 + 32j. Both lie on the line x - 2y = -76 of P§4, since b = (x + 76)/2 is the definition of Even.

## 4. The argument

**Theorem.** `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA` does not halt from the blank tape.

1. **Relation.** By Lemma R, this machine's run is σ of the parent's table run from `0^inf E> 0^inf` (section 1.3).

2. **Direct part.** That run reaches K(2583,70,76,43,18) after 6,950,830 steps without halting (section 2.1).

3. **Macro steps.** The parent's rules S, T6, TE, T8 and TO take it to Even(13299, 220) at step 163,638,058. Each application is inside its rule's domain (section 2.3).

4. **Double cycle.** From there the parent's double cycle applies forever (section 3, P§4). Each round takes at least one step (P§6).

5. **Conclusion.** So the parent's table run from E is infinite. By Lemma R this machine's run is too, step for step. ∎

**The halting cell.** Here only E1 = 1LF enters F. So this machine halts exactly when E reads a 1 that has a 0 on its left.

E1 is σ of the parent's A1 = 1LD, and Lemma R maps halts to halts. Every step of the run above lies inside the direct part or inside one of the parent's exact rules, and none of those halts (P§7.1).

**Not a cryptid.** As for the parent (P§7.2), the top-level map (n, x) ↦ (n + 12x + 808, x + 32) is affine and all its parities are fixed.

## 5. Remark: the starts of the table

The table has three entries in the 698 list.

| line | machine | start in the parent's table | mirror | Even reached |
|---|---|---|---|---|
| 202 | `1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF` | A | no | Even(12863, 212) at step 153,126,993 |
| 395 | `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF` | C | yes | Even(12857, 212) at step 153,013,640 |
| 599 | `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA` | E | no | Even(13299, 220) at step 163,638,058 |

Line 202 is the parent and line 395 is its mirrored sibling, each with its own proof. This write-up and the .v prove line 599.

Starts B and F give no further entries. On the blank tape, B0 = 0RC leaves the tape blank and enters C, and F0 = 0RB leaves it blank and enters B. So these runs are the start-C run, delayed by one or two steps.

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

The direct run of section 2.1 is

```
init : E;; tape0 -->* Kr 1291 35 38 21 9
```

since Kr 1291 35 38 21 9 = K(2583,70,76,43,18). It runs on busycoq's list configurations (`cconfig_step`), with the parent's nested step counter `cc_steps'` (P§8.4).

The run is cut at nine left records of `tmP`, where the tape is short in run-length form (12 to 20 pairs). That keeps every single computation about as large as the parent's longest piece. The first piece starts by writing `E;; tape0` as an empty list configuration in state E.

| piece | from | to | steps | ends at step |
|---|---|---|---|---|
| `init1` | `E;; tape0` | `LR W1` | 694,787 | 694,787 |
| `init2` | `LR W1` | `LR W2` | 683,978 | 1,378,765 |
| `init3` | `LR W2` | `LR W3` | 698,386 | 2,077,151 |
| `init4` | `LR W3` | `LR W4` | 690,894 | 2,768,045 |
| `init5` | `LR W4` | `LR W5` | 701,010 | 3,469,055 |
| `init6` | `LR W5` | `LR W6` | 686,460 | 4,155,515 |
| `init7` | `LR W6` | `LR W7` | 699,330 | 4,854,845 |
| `init8` | `LR W7` | `LR W8` | 697,792 | 5,552,637 |
| `init9` | `LR W8` | `LR W9` | 702,214 | 6,254,851 |
| `init10` | `LR W9` | `Kr 1291 35 38 21 9` | 695,979 | 6,950,830 |

Then `opening` follows the 18 rows of section 2.2 with the parent's lemmas. It ends at Ev 6649 21 = Even(13299, 220):

```
opening : Kr 1291 35 38 21 9 -->* Ev 6649 21
```

Its steps, two rows per line, read left to right:

```
follow (S_iter 8 1291 2 35 18 8).     follow (T6' 1483 13 4 16).
follow (S_iter 7 1779 1 53 14 8).     follow (TE' 1947 26 13).
follow (S_iter 6 2225 2 38 45 8).     follow (T6' 2369 12 31 12).
follow (S_iter 13 2665 3 49 14 8).    follow (T8' 2977 34 25).
follow (S_iter 10 3247 0 40 55 8).    follow (TO' 3487 22 40 20).
follow (S_iter 18 3781 3 57 14 8).    follow (T8' 4213 52 35).
follow (S_iter 14 4483 2 40 65 8).    follow (T6' 4819 30 51 28).
follow (S_iter 23 5115 1 65 14 8).    follow (TE' 5667 70 45).
follow (S_iter 17 5945 2 38 77 8).    follow (T6' 6353 34 63 34).
```

Each line holds two consecutive rows: an S block and the collision after it.

### 6.3 Non-halting for the parent's table from E

`nonhaltP : ~halts tmP (E;; tape0)` applies `multistep_nonhalt` with `init` and `opening`. Then it applies `progress_nonhalt_simple` from (6649, 21) with `DC` for each step, exactly as the parent does (P§8.5).

### 6.4 The relation

`phi` is σ⁻¹, from this machine's states to the parent's:

```
phi:   A -> E,   B -> F,   C -> B,   D -> C,   E -> A,   F -> D
```

The lemma `perm : Perm tm tmP phi` maps each defined transition as follows:

```
tm(q, s) = (w, d, t)  ->  tmP(phi q, s) = (w, d, phi t).
```

Undefined entries correspond too. The lemma holds by case analysis on the 12 cells.

`nonhalt` then needs one busycoq lemma:

```
halts tm c0   =   halts tm (A;; tape0)   ->   halts tmP (E;; tape0)
```

The equality is the definition of `c0`. The arrow is `perm_halts`, since phi A = E. Then `nonhaltP` gives the contradiction.

## 7. Numerical checks

They are evidence only; the result rests on the .v file alone.

- **Relation.** σ is the only map among the 720 renamings, with and without the mirror, and it matches all 12 cells. This machine and the parent's table from E run in lockstep, step for step, for 10⁷ steps, and their tapes are equal after 163,638,058 steps.
- **Opening.** Both runs reach their K configuration after 6,950,830 steps, with no earlier K-shaped left record in any state. Two independent scanners find the same 126 K-shaped left records up to step 163,638,058, for both runs.
- **Macro steps.** Those 126 records are exactly the start of section 2.2 and the result of every single rule application. Every row was also confirmed by direct simulation of this machine, and by one unbroken run to step 163,638,058.
- **Domains.** Every application in section 2.2 is inside its rule's domain, and the step numbers are the sums of the rules' step formulas.
- **Double cycle.** Whole double cycles of this machine from σEven(n, x), for every x = 4 (mod 8) from 52 to 404, give the exact configuration and step count of P§4.
- **Orbit.** From step 163,638,058 to 10¹⁰ steps, every Even member and every Odd member (the configuration after TE, P§4) was found by direct simulation of this machine. Each of the 1,606 K-shaped left records in that range is the next point predicted by S, TE or TO.
- **Halting.** No halt in the first 163,638,058 steps.
- **Remark.** Direct simulation of lines 214 and 418 reaches the Even members of section 5 at the steps shown there.

AI assistance: Claude (Anthropic) assisted with the original formal proofs, proof sketches, scripts and checks. GPT-6 Astra (OpenAI) assisted with independent audit and submission preparation.
