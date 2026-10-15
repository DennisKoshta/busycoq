# `1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF` never halts

This machine is a bouncer. Its head runs back and forth over a growing tape, from a fixed gadget at the left end to the right end of the written part and back.

Right of the gadget, the tape is five long blocks of 1s with four short words between them, the *particles*. How far a trip gets before a particle turns it back depends on the trip's phase, which repeats every 12 trips.

Every 12 trips the first block grows and the second one shrinks, so two particles drift toward each other. When they meet, a collision of 135 to 147 trips rebuilds the pattern with new block lengths.

Two kinds of collision alternate forever, and the block lengths follow an exact affine law from one pair of collisions to the next. Every piece of that law is an exact run of the machine, and none of them reaches the only undefined transition.

## Machine and status

- **Machine:** `1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF`, viewer https://bbchallenge.org/1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF
  - A BB(6) holdout: line 202 of the 698-machine list. Spreadsheet class "Bouncer + Chaotic Edge". The edge is not chaotic: it follows the closed law of §4.
  - The proof is written for the string itself, with no mirror and no renaming. Its only undefined transition is D0.
- **Template:** `verify/TranslatedBellv5.v`, `Module TM1` (`1RB0LA_1LC1LA_0RD0LB_0RE1RC_1LB0RF_1RD---`).
  - Shared: block macro rules, each proved for its whole domain by one ES_v3 `es'`, then repeated by induction and chained with `follow`.
  - Different: TM1's configurations carry lists of block lengths, and its top level needs an invariant (`progress_nonhalt_cond`).
  - Here every configuration has exactly five block lengths, and the top level is the family Even(n, x) of §4, which needs no invariant. So the proof ends with `progress_nonhalt_simple`, as in `verify/Bouncer_v2.v`, `Module TM1`.
  - New: a 4,097,897-step opening. It runs on busycoq's list configurations (`cconfig_step`) with nested step counters, as in `verify/Bouncer_v3.v`'s `multistep_c'`, and it is cut into six pieces.
- **Status:** formalized. The accompanying .v (361 lines) proves `Lemma nonhalt: ~halts tm c0.` in Coq 8.20.1 against unmodified busycoq BB6. It imports `Individual62`, `ES_v3` and the Coq standard library.
  - `Print Assumptions nonhalt`: *Closed under the global context*.


### Where each part lives in the .v

The .v has three banner comments: *Macro rules*, *The double cycle* and *Opening*. Every lemma is top level. §8 describes the .v in more detail.

| part of this write-up | .v part | names in the .v |
|---|---|---|
| §2 the gadget G and the family K (on half-length parameters, §8.1) | before the banners | `G`, `Kr` |
| §3.1 shift rules R1, R2b | inside the macro rules | found by `es'` itself, not stated separately |
| §3.3 rule S | Macro rules | `S_step`, `S_step'`, `S_iter` |
| §3.4 collision rules | Macro rules | `TE`, `TO`, `T6`, `T8` and their `-->*` forms `TE'` … `T8'` |
| §4 the double cycle | The double cycle | `Ev`, `prog_eq`, `DC` |
| §5 the direct run | Opening | `cc_steps`, `cc_steps'`, `rl`, `LR`, `Kr_list`, `Kr_cc`, `W1` … `W5`, `init1` … `init6`, `init` |
| §5 the 20 macro steps | Opening | `opening` |
| §6, §7.1 progress and non-halting | after the banners | `nonhalt` |
| §1 rule table | closing comment | the same table |

## 0. Summary

The tape right of the gadget G holds five 1-blocks, of lengths n, a, b, c, d, separated by four particles. Every round trip starts at G. The head runs right over some of the blocks and is turned back by one of the particles.

Over 12 trips the first block grows by 48 and the second shrinks by 8 (rule S). So the particle after the second block drifts toward the particle before it. When the second block is down to 2, 4, 6 or 8 cells, one of four collision rules (TO, TE, T6, T8) rebuilds the pattern.

Two of the collisions, TE and TO, alternate forever. Together with the runs of S between them they form a double cycle on the family Even(n, x) (defined in §2):

```
Even(n, x)  -->  Even(n + 12x + 808, x + 32)        (n odd, x = 4 mod 8, x >= 52)
```

The run from the blank tape reaches `Even(12863, 212)` at step 153,126,993, after an opening of 4,097,897 steps and 20 more macro steps. From there the double cycle repeats forever. So the machine never halts.

| piece | argument | in the .v |
|---|---|---|
| shift rules R1, R2b (§3.1) | exact finite runs + induction | found by `es'` inside the rules below |
| macro rules S, TE, TO, T6, T8 (§3.3, §3.4) | exact for the whole domain, by symbolic execution; S, TE and TO also trip by trip (§3.3, Appendices A and B) | `S_step`, `TE`, `TO`, `T6`, `T8`: one `es'` each |
| double cycle (§4) | arithmetic on the rule domains | `S_iter`, `DC` |
| opening: 4,097,897 steps, then 20 macro steps to Even(12863,212) (§5) | exact | `init`, `opening` |
| D0 never read (§7.1) | follows from the above | `nonhalt` |

## 1. Rule table (busycoq comment-block style)

```
1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF        (only D0 undefined; D is entered only by A1 = 1LD)

G            = 0^2 1^2 0 1^4 0 1^2 0 1^6 0 1^2 0 1^5 0^2 1^2 0 1^5 0 1^2 0^2          (43 cells)
K(n,a,b,c,d) = 0^inf <F G 1^n 0 1^a 0110 1^b 0^6 1^c 0110 1111 0^6 1^d 0110 0110 111 0^inf
Even(n,x)    = K(n, x, (x+76)/2, 35, 18)

R1   C> 1 1         --> 1 0 C>             2 steps    C1 E1
R2b  0 1 0 B> 0 0 0 --> 0 B> 0 0 0 1 1     12 steps   B0 C0 A0 B1 C0 A1 D1 E0 F1 F1 F1 F0
     k-fold:  C> 1^(2k) --> (10)^k C>   (2k steps);   0 (10)^k B> 000 --> 0 B> 000 1^(2k)   (12k steps)

rule  from            to                            domain                                          steps                          trips
S     K(n,a,b,c,d) -> K(n+48,a-8,b+4,c,d+4)         n odd, a even >= 10, b even >= 6, c odd >= 7, d even >= 2   84n+84a+77b+70c+63d+13628   12
TE    K(n,4,b,35,d) -> K(n+556,b-86,82,d+51,18)     n odd, b even >= 88, d even >= 20                         966n+952b+812d+455332        138
TO    K(n,2,b,c,d) -> K(n+588,b+c-91,d+62,35,18)    n odd, b even >= 82, c odd >= 37, d even >= 18            1029n+1001b+987c+882d+458476 147
T6    K(n,6,b,c,d) -> K(n+592,b+c-91,d+62,35,18)    n odd, b even >= 82, c odd >= 35, d even >= 18            1029n+1008b+987c+882d+462814 147
T8    K(n,8,b,35,d) -> K(n+540,b-74,86,d+47,18)     n odd, b even >= 88, d even >= 20                         945n+938b+784d+446893        135

DC    Even(n,x) --S^((x-4)/8)--> K(.,4,x+36,35,(x+32)/2) --TE--> K(.,x-50,82,(x+134)/2,18)
                --S^((x-52)/8)--> K(.,2,(x+112)/2,(x+134)/2,(x-16)/2) --TO--> Even(n+12x+808, x+32)
      n odd, x = 4 mod 8, x >= 52; 3x+201 trips

start c0 -->(4,097,897) K(1959,34,68,45,18) --(S^4 TO S^4 T6 S^6 T8 S^5 T6 S^12 T8 S^9 TO S^17 T8 S^13 T6 S^22 TE S^16 T6)-->
      Even(12863,212) at step 153,126,993;  then DC forever (x = 212, 244, 276, ...)
```

## 2. Notation and families

**Configurations.** `l <S r` is state S reading the last cell of `l`; `l S> r` is state S reading the first cell of `r`. Words are written left to right. `w^k` is k copies of w, and `0^inf` is the blank tail.

**Rules.** `X --> Y` between configurations means an exact run of the machine. A rule on partial configurations, such as R1, holds for every left side and every right side: the run never reads a cell outside the written part.

**G** is the 43-cell word of §1. It is the same at the start of every trip.

**The family K.** For n, a, b, c, d ≥ 0,

```
K(n,a,b,c,d) = 0^inf <F G 1^n 0 1^a 0 1^2 0 1^b 0^6 1^c 0 1^2 0 1^4 0^6 1^d 0 1^2 0^2 1^2 0 1^3 0^inf
```

The head is in state F on the 0 just left of G, and everything left of it is blank. The five 1-blocks have lengths n, a, b, c, d.

**Particles.** The short words between the blocks are, from left to right:

- W = `0` (between n and a);
- P1 = `0 1^2 0` (between a and b);
- Q = `0^6` (between b and c);
- Q' = `0 1^2 0 1^4 0^6` (between c and d);
- E = `0 1^2 0^2 1^2 0 1^3` (after d, the right end).

**Trip.** A *left record* is a step at which the head visits a cell left of every cell visited before. Trips are counted by left records, two per trip, and K(...) is the configuration at the first left record of a trip. "j trips" means 2j left records.

**Even(n, x)** = K(n, x, (x+76)/2, 35, 18). It is used for n odd and x = 4 (mod 8), x ≥ 52.

## 3. Rules

### 3.1 The two shift rules

**R1.** For all left sides l and right sides r:

```
l C> 1 1 r  -->(2)  l 1 0 C> r          transitions C1 (1RE), E1 (0RC)
```

C reads 1, writes 1 and moves right in state E. E reads 1, writes 0 and moves right in state C. By induction on k, `C> 1^(2k) --> (10)^k C>` in 2k steps.

**R2b.** For all l and r:

```
l 0 1 0 B> 0 0 0 r  -->(12)  l 0 B> 0 0 0 1 1 r
```

Number the six written cells 0 to 5, so B starts on cell 3. The twelve transitions are:

| step | transition | head after | cells 0..5 after |
|---|---|---|---|
| 1 | B0 = 0RC | 4 | 010000 |
| 2 | C0 = 1LA | 3 | 010010 |
| 3 | A0 = 1RB | 4 | 010110 |
| 4 | B1 = 1RC | 5 | 010110 |
| 5 | C0 = 1LA | 4 | 010111 |
| 6 | A1 = 1LD | 3 | 010111 |
| 7 | D1 = 1LE | 2 | 010111 |
| 8 | E0 = 1RF | 3 | 011111 |
| 9 | F1 = 0LF | 2 | 011011 |
| 10 | F1 = 0LF | 1 | 010011 |
| 11 | F1 = 0LF | 0 | 000011 |
| 12 | F0 = 0RB | 1 | 000011 |

- The head stays on cells 0..5, so the rule holds for every l and r.
- Cell 0 must be 0. With a 1 there, step 12 is F1 = 0LF instead, and the run goes elsewhere.
- **k-fold form.** `0 (10)^k B> 000 --> 0 B> 000 1^(2k)` in 12k steps, by induction on k. In `0 (10)^(k+1) B> 000 = 0 (10)^k 1 0 B> 000`, the cell left of the last copy is the 0 of the copy before it (or the leading 0 when k = 0). So R2b applies to the last copy, giving `0 (10)^k B> 000 11`, and the induction hypothesis finishes.

**Not used: R2a.** The machine also satisfies `0 10 11 C> 0 --> 0 11 C> 0 11` (12 steps). No proof below uses it: every macro rule closes with R1 and R2b alone.

### 3.2 How the macro rules are proved: symbolic execution

Each macro rule is a statement "for all values of the variables in the domain, start → end in exactly N steps". It is proved the way busycoq's ES_v3 `es'` proves block rules.

**Symbolic tapes.** A tape is a finite list of tokens between two blank tails:
- a single 0 cell;
- a run `1^L`;
- a block `(10)^X`.

L and X are linear forms in variables over ℕ with nonnegative coefficients, so each form is at least its constant term. Each domain variable is written by its parity and lower bound; for example a even ≥ 10 is a = 2a' + 10 with a' ≥ 0.

**Moves.** Each move is either an identity of tapes or an exact run of the machine.

| move | what it does | why it is sound |
|---|---|---|
| peel | take one concrete cell off a run whose constant term is ≥ 1 | `1^L = 1 1^(L-1)`, `(10)^X = 1 0 (10)^(X-1)` (read from the side the head is on) |
| merge | join adjacent 1-runs; `(10)^X 1 0 = (10)^(X+1)` | identity |
| step | one transition of the table on a concrete head cell | the table; a `---` stops the proof |
| R1 | `C> 1^(2h+c) --> (10)^h C> 1^c` on the symbolic part of a run | §3.1, 2h steps |
| R2b | `0 (10)^X B> 000 --> 0 B> 000 1^(2X)` on the symbolic part of a block | §3.1, 12X steps; the 0 is the last cell of the block's constant copies, or the cell below the block must be a 0 cell or the blank tail |
| split | v = 0, or v = v' + 1 | covers every v in ℕ |

A split happens only when the head must read a cell of a run or block whose constant term is 0.

**Leaves.** Each branch runs until the stated number of left records. Then it must match the claimed end configuration exactly, as a word (after merging runs), with the head on the leftmost cell and in state F.

The step count of a branch is a linear form, and it must equal the claimed formula. The rule holds because the branches cover the domain and each branch is a chain of exact runs and tape identities.

**In the .v,** each macro rule is one `es'` call. It runs this kind of symbolic execution inside Coq, and it finds the shift rules it needs by itself.

### 3.3 Rule S, trip by trip

S is the composition of twelve one-trip rules P1, ..., P12 between the phase families below. Every phase family has the form `K_j = 0^inf <F G w_j 0^inf` (G as in §1), and K_0 = K(n,a,b,c,d). All phases use the domain of S: n odd, a even ≥ 10, b even ≥ 6, c odd ≥ 7, d even ≥ 2.

| j | w_j (the word after G) | steps of P(j+1): K_j → K_(j+1) |
|---|---|---|
| 0 | `1^n 0 1^a 0 1^2 0 1^b 0^6 1^c 0 1^2 0 1^4 0^6 1^d 0 1^2 0^2 1^2 0 1^3` | 7n+7a+7b+14c+14d+1135 |
| 1 | `1^(n+3) 0^3 1^(a-2) 0^6 1^(b-2) 0^2 1^2 0^2 1^(c+3) 0^3 1^2 0^2 1^2 0^2 1^(d+2) 0 1^2 0 1^6 0 1^2` | 7n+14a+28b+14c+21d+1459 |
| 2 | `1^(n+7) 0 1^2 0^2 1^(a-4) 0^2 1^4 0^6 1^(b-1) 0 1^2 0 1^(c-1) 0^6 1^6 0^6 1^(d+5)` | 7n+841 |
| 3 | `1^(n+12) 0^2 1^(a-4) 0^2 1^4 0^6 1^(b-1) 0 1^2 0 1^(c-1) 0^6 1^6 0^6 1^(d+5)` | 7n+14a+7b+933 |
| 4 | `1^(n+15) 0^2 1^(a-2) 0^12 1^(b-1) 0 1^(c-1) 0^6 1^6 0^6 1^(d+5)` | 7n+7a+897 |
| 5 | `1^(n+19) 0 1^2 0 1^(a-4) 0 1^2 0^7 1^(b-1) 0 1^(c-1) 0^6 1^6 0^6 1^(d+5)` | 7n+925 |
| 6 | `1^(n+24) 0 1^(a-4) 0 1^2 0^7 1^(b-1) 0 1^(c-1) 0^6 1^6 0^6 1^(d+5)` | 7n+7a+971 |
| 7 | `1^(n+27) 0^3 1^(a-6) 0^2 1^4 0 1^(b+1) 0 1^(c-1) 0^6 1^6 0^6 1^(d+5)` | 7n+14a+21b+28c+28d+2247 |
| 8 | `1^(n+31) 0 1^2 0^2 1^(a-8) 0^2 1^(b+8) 0^2 1^(c-1) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3` | 7n+1009 |
| 9 | `1^(n+36) 0^2 1^(a-8) 0^2 1^(b+8) 0^2 1^(c-1) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3` | 7n+14a+14b+14c+1081 |
| 10 | `1^(n+39) 0^2 1^(a-6) 0^6 1^(b+4) 0^6 1^c 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3` | 7n+7a+1037 |
| 11 | `1^(n+43) 0 1^2 0 1^(a-8) 0 1^2 0 1^(b+4) 0^6 1^c 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3` | 7n+1093 |
| 12 | `1^(n+48) 0 1^(a-8) 0 1^2 0 1^(b+4) 0^6 1^c 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3` | (= K(n+48, a-8, b+4, c, d+4)) |

How to read the table:
- A block crossed once in each direction costs 7 steps per cell: 1 per cell by R1 going right, 6 per cell by R2b going left. So the coefficients show how far each trip goes. Trips 3, 6, 9 and 12 cost 7n + const: the head crosses only the first block and turns back at the particle right after it.
- The steps add up to S's formula: 84n+84a+77b+70c+63d+13628.

**Case split.** A symbolic run that reads the `(10)^X` block cell by cell has to split once, on d: d = 2 or d ≥ 4. The split happens in trip 1, where the head reads the `(10)^X` block made from the d block, and X may be 0. Both branches reach the same K_1, with the same step formula, so the table holds for all d ≥ 2. P2 to P12 need no split.

The split is not needed if a block is rotated before the head reads it:

```
y (v y)^X  =  (y v)^X y
```

This moves a concrete cell from one side of the block to the other. With this rotation P1, and so S, goes through in one branch. busycoq's `es'` rotates blocks this way, and the .v proves S with no case split.

**Domain.** Each lower bound of S is sharp. One below it (a = 8, b = 4, c = 5 or d = 0, same parity), the result is not K(n+48,a-8,b+4,c,d+4) in any case we sampled by direct simulation. a = 8 is where T8 takes over.

### 3.4 The collision rules TE, TO, T6, T8

When the second block is down to a ∈ {2, 4, 6, 8}, P1 has reached W, and S does not apply. One of four collision rules follows; their statements are in §1.

| rule | when | trips | steps | case splits | concrete steps of the symbolic run | R1 / R2b uses |
|---|---|---|---|---|---|---|
| TE | a = 4, c = 35 | 138 | 966n+952b+812d+455332 | none | 556,314 | 390 / 390 |
| TO | a = 2 | 147 | 1029n+1001b+987c+882d+458476 | none | 593,982 | 420 / 420 |
| T6 | a = 6 | 147 | 1029n+1008b+987c+882d+462814 | none | 596,920 | 421 / 421 |
| T8 | a = 8, c = 35 | 135 | 945n+938b+784d+446893 | none | 546,062 | 381 / 381 |

Each rule holds over its whole domain by one symbolic run (§3.2), with no case split. TE and TO carry the double cycle (§4); T6 and T8 are used only in the opening (§5).

**Trip by trip.** Appendices A and B list the configuration after every trip of TE and of TO, with the steps of each trip. Each row is a one-trip rule, like P1, ..., P12 in §3.3: from the configuration of the row above, the machine reaches the configuration of the row in exactly the steps shown, for every value in the rule's domain.

Each row can be checked by hand the way §3.3 is read: R1 across a variable block going right (it leaves a `(10)^X` block), R2b across that block going left, and single transitions everywhere else. The step column adds up to the rule's step formula.

**What happens in a collision.** The tables show the following.

- The variables occur only in the exponents of a few long 1-blocks: the first block, and the blocks that come from b and d (and c, in TO). Every other exponent is a constant.
- Every trip crosses the first block: every step count contains 7n.
- In TO, the b and c blocks merge into one block at trip 10.
- From trip 12 on, the left part grows and shrinks as in S. At rows 24, 36, 48, ... the first block is 48 longer than 12 rows before, and the block that came from b (in TO, from b and c) is 8 shorter. At the end that block is the new second block: b - 86 in TE, b + c - 91 in TO.
- Right of the d block, the word is a constant in every row. The head reaches it only on the trips whose step count contains d. On those trips it rebuilds the right end through the constant words shown, and the last row ends in E again.

**T6 and T8** are used only at the seven concrete arguments of §5. Their trip tables have the same form as those of TE and TO and are not printed here.

**The bounds are sufficient, not minimal.** Only the domains stated are claimed. For example TE also holds at d = 18 in the cases we sampled, which nothing below uses.

**In the .v** the four collision rules, like S, are proved over their whole domains, each by one `es'`. These `es'` lemmas are the certificate. The tables are for a human reader.

## 4. The double cycle

**Lemma DC.** Let n be odd, x = 4 (mod 8) and x ≥ 52. Write m = (x-4)/8 and m' = (x-52)/8. Then

```
Even(n, x)  -->  Even(n + 12x + 808, x + 32)
```

by the chain S^m, TE, S^(m'), TO, in 12m + 138 + 12m' + 147 = 3x + 201 trips.

*Proof.* We check each rule's domain at each application.

**Step 1: S, m times.** Before the i-th application (0 ≤ i < m) the configuration is

```
K(n + 48i, x - 8i, (x+76)/2 + 4i, 35, 18 + 4i)
```

- n + 48i is odd.
- x - 8i is even and at least x - 8(m-1) = 12 ≥ 10.
- x + 76 = 0 (mod 8), so (x+76)/2 + 4i is a multiple of 4, hence even, and it is ≥ 6.
- 35 is odd and ≥ 7; 18 + 4i is even and ≥ 2.

After m applications, with 4m = (x-4)/2:

```
K(n + 48m, 4, x + 36, 35, (x+32)/2)
```

**Step 2: TE.** a = 4 and c = 35 hold.
- b = x + 36 is even, and b ≥ 88 exactly when x ≥ 52.
- x + 32 = 4 (mod 8), so d = (x+32)/2 = 2 (mod 4) is even, and d ≥ 20 since x ≥ 8.

The result is

```
Odd = K(n + 48m + 556, x - 50, 82, (x+134)/2, 18)
```

**Step 3: S, m' times.** Before the i-th application the configuration is K(·, x - 50 - 8i, 82 + 4i, (x+134)/2, 18 + 4i).
- x - 50 - 8i is even and at least x - 50 - 8(m'-1) = 10.
- x + 134 = 2 (mod 8), so c = (x+134)/2 = 1 (mod 4) is odd, and c ≥ 7.
- b and d are even and ≥ 6 and ≥ 2.

After m' applications, with 4m' = (x-52)/2:

```
K(n + 48(m+m') + 556, 2, (x+112)/2, (x+134)/2, (x-16)/2)
```

**Step 4: TO.** a = 2 holds.
- x + 112 = 4 (mod 8), so b = (x+112)/2 is even; b ≥ 82 exactly when x ≥ 52.
- c = (x+134)/2 is odd (step 3) and ≥ 37.
- x - 16 = 4 (mod 8), so d = (x-16)/2 is even; d ≥ 18 exactly when x ≥ 52.

TO gives K(n'', b + c - 91, d + 62, 35, 18), where

```
b + c - 91 = (x+112)/2 + (x+134)/2 - 91 = x + 32
d + 62     = (x-16)/2 + 62 = (x+108)/2 = ((x+32) + 76)/2
n''        = n + 48(m+m') + 556 + 588 = n + 6(x-4) + 6(x-52) + 1144 = n + 12x + 808
```

So the result is Even(n + 12x + 808, x + 32). ∎

**Closure.** n + 12x + 808 is odd, x + 32 = 4 (mod 8) and x + 32 ≥ 52. So DC applies again, forever. The Even family with these conditions needs no further invariant: the conditions are the whole domain of DC, and DC preserves them.

**Remark.** The general two-parameter map behind DC, (x, y) ↦ (3x/4 + y/2 + 13, x/4 + y/2 + 35) for K(n, x, y, 35, 18), is an empirical observation. It keeps the line x - 2y = -76, which is the Even family. Nothing below uses the general map.

## 5. Initial segment (exact)

**Opening.** From the blank tape `0^inf A> 0^inf`, the machine reaches K(1959,34,68,45,18) after exactly 4,097,897 steps, by direct simulation. This is the first left record whose configuration is in the K family.

**Macro steps.** From there, 20 macro steps reach Even(12863,212). Each row applies its rule as many times as shown. Every application is inside its rule's domain, and the step numbers are the sums of the step formulas. Each row's configuration was also confirmed by direct simulation at exactly that step.

| after | rule | step | configuration |
|---|---|---|---|
| opening | (direct run) | 4,097,897 | K(1959,34,68,45,18) |
| 1 | S^4 | 4,883,657 | K(2151,2,84,45,34) |
| 2 | TO | 7,713,999 | K(2739,38,96,35,18) |
| 3 | S^4 | 8,769,007 | K(2931,6,112,35,34) |
| 4 | T6 | 12,425,249 | K(3523,56,96,35,18) |
| 5 | S^6 | 14,435,489 | K(3811,8,120,35,42) |
| 6 | T8 | 18,629,265 | K(4351,46,86,89,18) |
| 7 | S^5 | 20,653,275 | K(4591,6,106,89,38) |
| 8 | T6 | 26,068,435 | K(5183,104,100,35,18) |
| 9 | S^12 | 31,955,395 | K(5759,8,148,35,66) |
| 10 | T8 | 38,035,111 | K(6299,74,86,113,18) |
| 11 | S^9 | 43,257,865 | K(6731,2,122,113,54) |
| 12 | TO | 50,923,821 | K(7319,144,116,35,18) |
| 13 | S^17 | 62,558,553 | K(8135,8,184,35,86) |
| 14 | T8 | 70,933,037 | K(8675,110,86,133,18) |
| 15 | S^13 | 81,231,039 | K(9299,6,138,133,70) |
| 16 | T6 | 91,594,639 | K(9891,180,132,35,18) |
| 17 | S^22 | 111,713,639 | K(10947,4,220,35,106) |
| 18 | TE | 123,039,285 | K(11503,134,82,157,18) |
| 19 | S^16 | 139,662,869 | K(12271,6,146,157,82) |
| 20 | T6 | 153,126,993 | K(12863,212,144,35,18) |

The last row is Even(12863, 212): (212 + 76)/2 = 144, 12863 is odd, and 212 = 4 (mod 8) with 212 ≥ 52.

Before row 20 the run is not in the Even family. For example row 16, K(9891,180,132,35,18), has b = 132 where Even would need (180+76)/2 = 128. The early runs end with all four collision types, which is why the opening needs T6 and T8.

## 6. Coverage and progress

- **Coverage.** There is no case analysis at the top level. From step 153,126,993, each application of DC starts and ends in the Even family (§4, closure). Every Even member satisfies DC's hypotheses. Inside DC, each application's domain is checked in §4. The opening is a fixed finite list (§5).
- **Progress.** Every macro rule takes at least 15,630 steps (the minimum for S on its domain), so each DC round takes at least one step. Progress is never a 0-step round.

## 7. Conclusion

### 7.1 Non-halting

1. c0 = `0^inf A> 0^inf` reaches Even(12863, 212) at step 153,126,993 (§5).
2. Each Even member reaches the next by an exact run of at least one step (§4), and the next one is again an Even member.
3. So the run is infinite.

**Why D0 is never read.** D0 is the only undefined transition. D is entered only by A1 = 1LD, so the machine halts exactly when A reads a 1 that has a 0 on its left.

Every step of the run is inside one of the exact runs above. These are the opening (a direct run that does not halt), the shift rules (their transitions are listed in §3.1, and D0 is not among them) and the concrete steps of the symbolic runs (a symbolic run stops with a failure on `---`, and none does).

### 7.2 Why it is not a cryptid

The top-level map is affine: (n, x) ↦ (n + 12x + 808, x + 32). All parities are fixed (n odd, x = 4 mod 8). No branch depends on the digits of a growing number, so nothing in the argument depends on an unpredictable sequence.

### 7.3 Siblings (remark)

The same table, started in other states, gives two more entries of the 698 list:

- line 395, `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF`: this table started in C, mirrored. By direct simulation it reaches Even(12857, 212) at step 153,013,640.
- line 599, `1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA`: this table started in E, not mirrored. By direct simulation it reaches Even(13299, 220) at step 163,638,058.

Both x values are 4 (mod 8) and ≥ 52, so §4 applies after their own openings. The accompanying [mirrored-start proof](1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF_writeup.md) and [E-start proof](1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA_writeup.md) establish those openings and non-halting results. This write-up and its .v prove the A-start machine.

## 8. The proof in Rocq

The .v proves the rules of this write-up on half-length parameters, and it ends with busycoq's `progress_nonhalt_simple`.

### 8.1 Half-length parameters

All lemmas are stated on half-length parameters, so that every block is `[1;1]^^k`:

```
Kr n a b c d  :=  K(2n+1, 2a, 2b, 2c+1, 2d)
  = 0inf <{{F}} G *> [1] *> [1;1]^^n *> [0] *> [1;1]^^a *> [0;1;1;0] *> [1;1]^^b *> [0;0;0;0;0;0]
         *> [1] *> [1;1]^^c *> [0;1;1;0;1;1;1;1;0;0;0;0;0;0] *> [1;1]^^d *> [0;1;1;0;0;1;1;0;1;1;1] *> 0inf
Ev N X  :=  Even(2N+1, 8X+52)  =  Kr N (4X+26) (2X+32) 17 9
```

The parities of §1 are then built into the definition. The lower bounds are built into the arguments of each lemma: for example a even ≥ 10 becomes `Kr n (5+a) ...`.

### 8.2 Macro rules

Each rule is one `es'` call, with no `destruct`. Before it runs, the hook `es_v3_pre` unfolds `Kr` and `G`. `es'` proves each rule for its whole domain by symbolic execution, with shift rules that it finds itself (compare §3.1 and §3.2).

| lemma | statement |
|---|---|
| `S_step n a b c d` | `Kr n (5+a) (3+b) (3+c) (1+d) -->+ Kr (24+n) (1+a) (5+b) (3+c) (3+d)` |
| `TE n b d` | `Kr n 2 (44+b) 17 (10+d) -->+ Kr (278+n) (1+b) 41 (35+d) 9` |
| `TO n b c d` | `Kr n 1 (41+b) (18+c) (9+d) -->+ Kr (294+n) (14+b+c) (40+d) 17 9` |
| `T6 n b c d` | `Kr n 3 (41+b) (17+c) (9+d) -->+ Kr (296+n) (13+b+c) (40+d) 17 9` |
| `T8 n b d` | `Kr n 4 (44+b) 17 (10+d) -->+ Kr (270+n) (7+b) 43 (33+d) 9` |

The primed forms `S_step'`, `TE'`, … `T8'` are the same statements with `-->*`. S is iterated by induction on k (`S_iter`):

```
S_iter k n a b c d :  Kr n (4*k+1+a) (3+b) (3+c) (1+d) -->* Kr (24*k+n) (1+a) (2*k+3+b) (3+c) (2*k+1+d)
```

### 8.3 The double cycle

`DC N X : Ev N X -->+ Ev (48*X+716+N) (4+X)`. X grows by 4 because x grows by 32. The proof is `follow` through four lemmas:

| lemma | arguments |
|---|---|
| `S_iter` | k = X+6, n = N, a = 1, b = 2X+29, c = 14, d = 8 |
| `TE'` | n = 24(X+6)+N, b = 4X, d = 2X+11 |
| `S_iter` | k = X, n = 278+24(X+6)+N, a = 0, b = 38, c = 2X+43, d = 8 |
| `TO` | n = 24X+278+24(X+6)+N, b = 2X, c = 2X+28, d = 2X |

The last lemma's start and end equal the configurations of the chain only up to arithmetic. `prog_eq` rewrites both with `lia_refl`.

### 8.4 Opening

`init : c0 -->* Kr 979 17 34 22 9` is the 4,097,897-step direct run of §5 (Kr 979 17 34 22 9 = K(1959,34,68,45,18)). It runs on busycoq's list configurations (`cconfig_step`).

The step counter is nested as in `verify/Bouncer_v3.v`'s `multistep_c'`: `cc_steps' n1 1000 n3` runs n1 rounds of 1,000 steps and then n3 more. Each piece is closed by `vm_compute; reflexivity`.

The run is cut at five left records. There the tape is short in run-length form (15 to 19 pairs), and `rl` writes it out: `LR W_k` is F reading the leftmost visited cell, with the word `rl W_k` to its right. The cut keeps each kernel computation small enough for coqchk to re-check it.

| piece | from | to | steps | ends at step |
|---|---|---|---|---|
| `init1` | `c0` | `LR W1` | 694,884 | 694,884 |
| `init2` | `LR W1` | `LR W2` | 702,616 | 1,397,500 |
| `init3` | `LR W2` | `LR W3` | 702,120 | 2,099,620 |
| `init4` | `LR W3` | `LR W4` | 690,676 | 2,790,296 |
| `init5` | `LR W4` | `LR W5` | 702,744 | 3,493,040 |
| `init6` | `LR W5` | `Kr 979 17 34 22 9` | 604,857 | 4,097,897 |

The last piece ends at a K configuration; `Kr_cc` writes it as a list configuration.

Then `opening` follows the 20 rows of §5, each by an iterated S or a collision rule at concrete arguments. It ends at Even(12863, 212):

```
opening : Kr 979 17 34 22 9 -->* Ev 6431 20
```

### 8.5 Non-halting

`nonhalt` applies `multistep_nonhalt` with `init` and `opening`. Then it applies `progress_nonhalt_simple` with

```
A := (nat * nat),   C := fun p => Ev (fst p) (snd p),   start (6431, 20),   witness (48*X+716+N, 4+X)
```

and `DC` for each step. No invariant is needed, because every pair (N, X) is in DC's domain (§6).

## Appendix A. TE trip by trip

The rule, for n odd, b even ≥ 88 and d even ≥ 20:

```
TE:  K(n,4,b,35,d)  -->  K(n+556, b-86, 82, d+51, 18)      in 966n+952b+812d+455332 steps, 138 trips
```

Row j gives the configuration after j trips, `0^inf <F G w 0^inf`, by its word w after G. Row 0 is K(n,4,b,35,d), and row 138 is K(n+556, b-86, 82, d+51, 18).

The steps of trip j take row j-1 to row j. They add up to the step formula of TE. On the whole domain every exponent is at least 1, so each row is a word of the shape shown.

```
trip  steps of the trip      w (the word after G)
   0  -                      1^n 0 1^4 0 1^2 0 1^b 0^6 1^35 0 1^2 0 1^4 0^6 1^d 0 1^2 0^2 1^2 0 1^3
   1  7n+7b+14d+1653         1^(n+3) 0^3 1^2 0^6 1^(b-2) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^2 1^(d+2) 0 1^2 0 1^6 0 1^2
   2  7n+21b+21d+1963        1^(n+7) 0 1^2 0 1^6 0 1^2 0 1^(b-1) 0 1^2 0 1^2 0 1^34 0^6 1^6 0^6 1^(d+5)
   3  7n+841                 1^(n+12) 0 1^6 0 1^2 0 1^(b-1) 0 1^2 0 1^2 0 1^34 0^6 1^6 0^6 1^(d+5)
   4  7n+7b+907              1^(n+15) 0^3 1^4 0^6 1^(b-1) 0 1^2 0 1^34 0^6 1^6 0^6 1^(d+5)
   5  7n+28b+28d+3227        1^(n+19) 0 1^2 0^2 1^2 0^2 1^4 0^6 1^(b-2) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
   6  7n+925                 1^(n+24) 0^2 1^2 0^2 1^4 0^6 1^(b-2) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
   7  7n+7b+1637             1^(n+27) 0^2 1^4 0^12 1^(b-4) 0^2 1^41 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
   8  7n+1023                1^(n+31) 0 1^2 0 1^2 0 1^2 0^7 1^(b-4) 0^2 1^41 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
   9  7n+1009                1^(n+36) 0 1^2 0 1^2 0^7 1^(b-4) 0^2 1^41 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
  10  7n+1097                1^(n+39) 0^5 1^4 0 1^(b-2) 0^2 1^41 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
  11  7n+1075                1^(n+43) 0 1^6 0 1^(b-2) 0^2 1^41 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
  12  7n+1093                1^(n+52) 0 1^(b-2) 0^2 1^41 0 1^2 0 1^4 0^6 1^(d+4) 0 1^2 0^2 1^2 0 1^3
  13  7n+7b+28d+2321         1^(n+55) 0^3 1^(b-4) 0^2 1^42 0^2 1^2 0^6 1^4 0^6 1^(d+9) 0 1^2
  14  7n+14b+28d+3357        1^(n+59) 0 1^2 0^2 1^(b-6) 0^2 1^46 0^6 1^4 0^2 1^4 0^6 1^(d+8) 0^2 1^8
  15  7n+1205                1^(n+64) 0^2 1^(b-6) 0^2 1^46 0^6 1^4 0^2 1^4 0^6 1^(d+8) 0^2 1^8
  16  7n+14b+7d+2303         1^(n+67) 0^2 1^(b-4) 0^6 1^42 0^6 1^2 0^2 1^6 0^6 1^(d+6) 0^2 1^10 0^2 1^4 0 1^2
  17  7n+7b+1247             1^(n+71) 0 1^2 0 1^(b-6) 0 1^2 0 1^42 0^6 1^2 0^2 1^6 0^6 1^(d+6) 0^2 1^10 0^2 1^4 0 1^2
  18  7n+1289                1^(n+76) 0 1^(b-6) 0 1^2 0 1^42 0^6 1^2 0^2 1^6 0^6 1^(d+6) 0^2 1^10 0^2 1^4 0 1^2
  19  7n+7b+7d+2121          1^(n+79) 0^3 1^(b-8) 0^6 1^40 0^2 1^2 0^6 1^8 0^6 1^(d+4) 0^2 1^12 0^6 1^2 0 1^2
  20  7n+14b+14d+3351        1^(n+83) 0 1^2 0^2 1^(b-10) 0^2 1^4 0^6 1^41 0 1^2 0 1^6 0^2 1^2 0^2 1^(d+6) 0 1^2 0 1^12 0 1^2 0^3 1^4 0 1^2
  21  7n+1373                1^(n+88) 0^2 1^(b-10) 0^2 1^4 0^6 1^41 0 1^2 0 1^6 0^2 1^2 0^2 1^(d+6) 0 1^2 0 1^12 0 1^2 0^3 1^4 0 1^2
  22  7n+14b+1675            1^(n+91) 0^2 1^(b-8) 0^12 1^41 0 1^6 0^2 1^2 0^2 1^(d+6) 0 1^2 0 1^12 0 1^2 0^3 1^4 0 1^2
  23  7n+7b+1387             1^(n+95) 0 1^2 0 1^(b-10) 0 1^2 0^7 1^41 0 1^6 0^2 1^2 0^2 1^(d+6) 0 1^2 0 1^12 0 1^2 0^3 1^4 0 1^2
  24  7n+1457                1^(n+100) 0 1^(b-10) 0 1^2 0^7 1^41 0 1^6 0^2 1^2 0^2 1^(d+6) 0 1^2 0 1^12 0 1^2 0^3 1^4 0 1^2
  25  7n+7b+1461             1^(n+103) 0^3 1^(b-12) 0^2 1^4 0 1^43 0 1^6 0^2 1^2 0^2 1^(d+6) 0 1^2 0 1^12 0 1^2 0^3 1^4 0 1^2
  26  7n+14b+28d+3675        1^(n+107) 0 1^2 0^2 1^(b-14) 0^2 1^50 0^2 1^6 0 1^2 0 1^6 0 1^2 0 1^(d+14) 0 1^2 0^2 1^2 0^2 1^8 0 1^2
  27  7n+1541                1^(n+112) 0^2 1^(b-14) 0^2 1^50 0^2 1^6 0 1^2 0 1^6 0 1^2 0 1^(d+14) 0 1^2 0^2 1^2 0^2 1^8 0 1^2
  28  7n+14b+2215            1^(n+115) 0^2 1^(b-12) 0^6 1^46 0^6 1^9 0 1^2 0 1^(d+14) 0 1^2 0^2 1^2 0^2 1^8 0 1^2
  29  7n+7b+1527             1^(n+119) 0 1^2 0 1^(b-14) 0 1^2 0 1^46 0^6 1^9 0 1^2 0 1^(d+14) 0 1^2 0^2 1^2 0^2 1^8 0 1^2
  30  7n+1625                1^(n+124) 0 1^(b-14) 0 1^2 0 1^46 0^6 1^9 0 1^2 0 1^(d+14) 0 1^2 0^2 1^2 0^2 1^8 0 1^2
  31  7n+7b+7d+2317          1^(n+127) 0^3 1^(b-16) 0^6 1^44 0^2 1^2 0^2 1^12 0^3 1^(d+12) 0^2 1^6 0 1^2 0 1^7
  32  7n+14b+21d+4167        1^(n+131) 0 1^2 0^2 1^(b-18) 0^2 1^4 0^6 1^45 0 1^2 0 1^8 0^2 1^(d+14) 0 1^2 0 1^16 0 1^2 0 1^3
  33  7n+1709                1^(n+136) 0^2 1^(b-18) 0^2 1^4 0^6 1^45 0 1^2 0 1^8 0^2 1^(d+14) 0 1^2 0 1^16 0 1^2 0 1^3
  34  7n+14b+1927            1^(n+139) 0^2 1^(b-16) 0^12 1^45 0 1^8 0^2 1^(d+14) 0 1^2 0 1^16 0 1^2 0 1^3
  35  7n+7b+1667             1^(n+143) 0 1^2 0 1^(b-18) 0 1^2 0^7 1^45 0 1^8 0^2 1^(d+14) 0 1^2 0 1^16 0 1^2 0 1^3
  36  7n+1793                1^(n+148) 0 1^(b-18) 0 1^2 0^7 1^45 0 1^8 0^2 1^(d+14) 0 1^2 0 1^16 0 1^2 0 1^3
  37  7n+7b+1741             1^(n+151) 0^3 1^(b-20) 0^2 1^4 0 1^47 0 1^8 0^2 1^(d+14) 0 1^2 0 1^16 0 1^2 0 1^3
  38  7n+14b+49d+5007        1^(n+155) 0 1^2 0^2 1^(b-22) 0^2 1^54 0^2 1^8 0 1^2 0 1^(d+34) 0 1^2 0 1^8
  39  7n+1877                1^(n+160) 0^2 1^(b-22) 0^2 1^54 0^2 1^8 0 1^2 0 1^(d+34) 0 1^2 0 1^8
  40  7n+14b+2523            1^(n+163) 0^2 1^(b-20) 0^6 1^50 0^6 1^(d+39) 0 1^2 0 1^8
  41  7n+7b+1807             1^(n+167) 0 1^2 0 1^(b-22) 0 1^2 0 1^50 0^6 1^(d+39) 0 1^2 0 1^8
  42  7n+1961                1^(n+172) 0 1^(b-22) 0 1^2 0 1^50 0^6 1^(d+39) 0 1^2 0 1^8
  43  7n+7b+14d+3009         1^(n+175) 0^3 1^(b-24) 0^6 1^48 0^2 1^2 0^2 1^(d+42) 0^3 1^6 0^2 1^2 0^2 1^4 0 1^2
  44  7n+14b+14d+4541        1^(n+179) 0 1^2 0^2 1^(b-26) 0^2 1^4 0^6 1^49 0 1^2 0 1^(d+38) 0^2 1^8 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  45  7n+2045                1^(n+184) 0^2 1^(b-26) 0^2 1^4 0^6 1^49 0 1^2 0 1^(d+38) 0^2 1^8 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  46  7n+14b+2179            1^(n+187) 0^2 1^(b-24) 0^12 1^49 0 1^(d+38) 0^2 1^8 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  47  7n+7b+1947             1^(n+191) 0 1^2 0 1^(b-26) 0 1^2 0^7 1^49 0 1^(d+38) 0^2 1^8 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  48  7n+2129                1^(n+196) 0 1^(b-26) 0 1^2 0^7 1^49 0 1^(d+38) 0^2 1^8 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  49  7n+7b+2021             1^(n+199) 0^3 1^(b-28) 0^2 1^4 0 1^51 0 1^(d+38) 0^2 1^8 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  50  7n+14b+28d+5647        1^(n+203) 0 1^2 0^2 1^(b-30) 0^2 1^58 0^2 1^(d+38) 0 1^2 0 1^16 0 1^2 0 1^4 0^6 1^6 0 1^2
  51  7n+2213                1^(n+208) 0^2 1^(b-30) 0^2 1^58 0^2 1^(d+38) 0 1^2 0 1^16 0 1^2 0 1^4 0^6 1^6 0 1^2
  52  7n+14b+14d+3223        1^(n+211) 0^2 1^(b-28) 0^6 1^54 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^6 0 1^2
  53  7n+7b+2087             1^(n+215) 0 1^2 0 1^(b-30) 0 1^2 0 1^54 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^6 0 1^2
  54  7n+2297                1^(n+220) 0 1^(b-30) 0 1^2 0 1^54 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^6 0 1^2
  55  7n+7b+14d+3599         1^(n+223) 0^3 1^(b-32) 0^6 1^52 0^2 1^2 0^2 1^(d+54) 0^3 1^2 0^2 1^2 0^2 1^8 0 1^2 0 1^3
  56  7n+14b+14d+5025        1^(n+227) 0 1^2 0^2 1^(b-34) 0^2 1^4 0^6 1^53 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  57  7n+2381                1^(n+232) 0^2 1^(b-34) 0^2 1^4 0^6 1^53 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  58  7n+14b+2431            1^(n+235) 0^2 1^(b-32) 0^12 1^53 0 1^(d+50) 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  59  7n+7b+2227             1^(n+239) 0 1^2 0 1^(b-34) 0 1^2 0^7 1^53 0 1^(d+50) 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  60  7n+2465                1^(n+244) 0 1^(b-34) 0 1^2 0^7 1^53 0 1^(d+50) 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  61  7n+7b+2301             1^(n+247) 0^3 1^(b-36) 0^2 1^4 0 1^55 0 1^(d+50) 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  62  7n+14b+28d+6025        1^(n+251) 0 1^2 0^2 1^(b-38) 0^2 1^62 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  63  7n+2549                1^(n+256) 0^2 1^(b-38) 0^2 1^62 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  64  7n+14b+14d+3671        1^(n+259) 0^2 1^(b-36) 0^6 1^58 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  65  7n+7b+2367             1^(n+263) 0 1^2 0 1^(b-38) 0 1^2 0 1^58 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  66  7n+2633                1^(n+268) 0 1^(b-38) 0 1^2 0 1^58 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  67  7n+7b+14d+3989         1^(n+271) 0^3 1^(b-40) 0^6 1^56 0^2 1^2 0^2 1^(d+54) 0^3 1^2 0^2 1^2 0^2 1^6 0 1^2 0^2 1^2 0 1^3 0 1^3
  68  7n+14b+14d+5249        1^(n+275) 0 1^2 0^2 1^(b-42) 0^2 1^4 0^6 1^57 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  69  7n+2717                1^(n+280) 0^2 1^(b-42) 0^2 1^4 0^6 1^57 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  70  7n+14b+2683            1^(n+283) 0^2 1^(b-40) 0^12 1^57 0 1^(d+50) 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  71  7n+7b+2507             1^(n+287) 0 1^2 0 1^(b-42) 0 1^2 0^7 1^57 0 1^(d+50) 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  72  7n+2801                1^(n+292) 0 1^(b-42) 0 1^2 0^7 1^57 0 1^(d+50) 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  73  7n+7b+2581             1^(n+295) 0^3 1^(b-44) 0^2 1^4 0 1^59 0 1^(d+50) 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  74  7n+14b+28d+6177        1^(n+299) 0 1^2 0^2 1^(b-46) 0^2 1^66 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  75  7n+2885                1^(n+304) 0^2 1^(b-46) 0^2 1^66 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  76  7n+14b+14d+3951        1^(n+307) 0^2 1^(b-44) 0^6 1^62 0^6 1^(d+51) 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  77  7n+7b+2647             1^(n+311) 0 1^2 0 1^(b-46) 0 1^2 0 1^62 0^6 1^(d+51) 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  78  7n+2969                1^(n+316) 0 1^(b-46) 0 1^2 0 1^62 0^6 1^(d+51) 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  79  7n+7b+14d+4225         1^(n+319) 0^3 1^(b-48) 0^6 1^60 0^2 1^2 0^2 1^(d+54) 0^3 1^2 0^2 1^2 0^3 1^2 0^3 1^2 0^2 1^4 0^6 1^2 0 1^2
  80  7n+14b+14d+5761        1^(n+323) 0 1^2 0^2 1^(b-50) 0^2 1^4 0^6 1^61 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  81  7n+3053                1^(n+328) 0^2 1^(b-50) 0^2 1^4 0^6 1^61 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  82  7n+14b+2935            1^(n+331) 0^2 1^(b-48) 0^12 1^61 0 1^(d+50) 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  83  7n+7b+2787             1^(n+335) 0 1^2 0 1^(b-50) 0 1^2 0^7 1^61 0 1^(d+50) 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  84  7n+3137                1^(n+340) 0 1^(b-50) 0 1^2 0^7 1^61 0 1^(d+50) 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  85  7n+7b+2861             1^(n+343) 0^3 1^(b-52) 0^2 1^4 0 1^63 0 1^(d+50) 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  86  7n+14b+28d+6559        1^(n+347) 0 1^2 0^2 1^(b-54) 0^2 1^70 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^9 0 1^3
  87  7n+3221                1^(n+352) 0^2 1^(b-54) 0^2 1^70 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^9 0 1^3
  88  7n+14b+14d+4231        1^(n+355) 0^2 1^(b-52) 0^6 1^66 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^9 0 1^3
  89  7n+7b+2927             1^(n+359) 0 1^2 0 1^(b-54) 0 1^2 0 1^66 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^9 0 1^3
  90  7n+3305                1^(n+364) 0 1^(b-54) 0 1^2 0 1^66 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^9 0 1^3
  91  7n+7b+14d+4519         1^(n+367) 0^3 1^(b-56) 0^6 1^64 0^2 1^2 0^2 1^(d+54) 0^3 1^2 0^2 1^2 0^2 1^14 0 1^2
  92  7n+14b+14d+6085        1^(n+371) 0 1^2 0^2 1^(b-58) 0^2 1^4 0^6 1^65 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
  93  7n+3389                1^(n+376) 0^2 1^(b-58) 0^2 1^4 0^6 1^65 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
  94  7n+14b+3187            1^(n+379) 0^2 1^(b-56) 0^12 1^65 0 1^(d+50) 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
  95  7n+7b+3067             1^(n+383) 0 1^2 0 1^(b-58) 0 1^2 0^7 1^65 0 1^(d+50) 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
  96  7n+3473                1^(n+388) 0 1^(b-58) 0 1^2 0^7 1^65 0 1^(d+50) 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
  97  7n+7b+3141             1^(n+391) 0^3 1^(b-60) 0^2 1^4 0 1^67 0 1^(d+50) 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
  98  7n+14b+28d+7043        1^(n+395) 0 1^2 0^2 1^(b-62) 0^2 1^74 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
  99  7n+3557                1^(n+400) 0^2 1^(b-62) 0^2 1^74 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 100  7n+14b+14d+4511        1^(n+403) 0^2 1^(b-60) 0^6 1^70 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 101  7n+7b+3207             1^(n+407) 0 1^2 0 1^(b-62) 0 1^2 0 1^70 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 102  7n+3641                1^(n+412) 0 1^(b-62) 0 1^2 0 1^70 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 103  7n+7b+14d+5059         1^(n+415) 0^3 1^(b-64) 0^6 1^68 0^2 1^2 0^2 1^(d+54) 0^3 1^2 0^2 1^2 0^2 1^10 0 1^2 0 1^6 0^2 1^2 0^2 1^4 0 1^2
 104  7n+14b+14d+6367        1^(n+419) 0 1^2 0^2 1^(b-66) 0^2 1^4 0^6 1^69 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 105  7n+3725                1^(n+424) 0^2 1^(b-66) 0^2 1^4 0^6 1^69 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 106  7n+14b+3439            1^(n+427) 0^2 1^(b-64) 0^12 1^69 0 1^(d+50) 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 107  7n+7b+3347             1^(n+431) 0 1^2 0 1^(b-66) 0 1^2 0^7 1^69 0 1^(d+50) 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 108  7n+3809                1^(n+436) 0 1^(b-66) 0 1^2 0^7 1^69 0 1^(d+50) 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 109  7n+7b+3421             1^(n+439) 0^3 1^(b-68) 0^2 1^4 0 1^71 0 1^(d+50) 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 110  7n+14b+28d+7361        1^(n+443) 0 1^2 0^2 1^(b-70) 0^2 1^78 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 111  7n+3893                1^(n+448) 0^2 1^(b-70) 0^2 1^78 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 112  7n+14b+14d+4791        1^(n+451) 0^2 1^(b-68) 0^6 1^74 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 113  7n+7b+3487             1^(n+455) 0 1^2 0 1^(b-70) 0 1^2 0 1^74 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 114  7n+3977                1^(n+460) 0 1^(b-70) 0 1^2 0 1^74 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 115  7n+7b+14d+5277         1^(n+463) 0^3 1^(b-72) 0^6 1^72 0^2 1^2 0^2 1^(d+54) 0^3 1^2 0^2 1^2 0^2 1^12 0 1^2 0 1^5 0 1^3
 116  7n+14b+14d+6713        1^(n+467) 0 1^2 0^2 1^(b-74) 0^2 1^4 0^6 1^73 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 117  7n+4061                1^(n+472) 0^2 1^(b-74) 0^2 1^4 0^6 1^73 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 118  7n+14b+3691            1^(n+475) 0^2 1^(b-72) 0^12 1^73 0 1^(d+50) 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 119  7n+7b+3627             1^(n+479) 0 1^2 0 1^(b-74) 0 1^2 0^7 1^73 0 1^(d+50) 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 120  7n+4145                1^(n+484) 0 1^(b-74) 0 1^2 0^7 1^73 0 1^(d+50) 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 121  7n+7b+3701             1^(n+487) 0^3 1^(b-76) 0^2 1^4 0 1^75 0 1^(d+50) 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 122  7n+14b+28d+7771        1^(n+491) 0 1^2 0^2 1^(b-78) 0^2 1^82 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 123  7n+4229                1^(n+496) 0^2 1^(b-78) 0^2 1^82 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 124  7n+14b+14d+5071        1^(n+499) 0^2 1^(b-76) 0^6 1^78 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 125  7n+7b+3767             1^(n+503) 0 1^2 0 1^(b-78) 0 1^2 0 1^78 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 126  7n+4313                1^(n+508) 0 1^(b-78) 0 1^2 0 1^78 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 127  7n+7b+14d+5675         1^(n+511) 0^3 1^(b-80) 0^6 1^76 0^2 1^2 0^2 1^(d+54) 0^3 1^2 0^2 1^2 0^2 1^12 0 1^2 0 1^10 0 1^2
 128  7n+14b+14d+7059        1^(n+515) 0 1^2 0^2 1^(b-82) 0^2 1^4 0^6 1^77 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^19
 129  7n+4397                1^(n+520) 0^2 1^(b-82) 0^2 1^4 0^6 1^77 0 1^2 0 1^(d+50) 0^6 1^6 0^6 1^19
 130  7n+14b+3943            1^(n+523) 0^2 1^(b-80) 0^12 1^77 0 1^(d+50) 0^6 1^6 0^6 1^19
 131  7n+7b+3907             1^(n+527) 0 1^2 0 1^(b-82) 0 1^2 0^7 1^77 0 1^(d+50) 0^6 1^6 0^6 1^19
 132  7n+4481                1^(n+532) 0 1^(b-82) 0 1^2 0^7 1^77 0 1^(d+50) 0^6 1^6 0^6 1^19
 133  7n+7b+3981             1^(n+535) 0^3 1^(b-84) 0^2 1^4 0 1^79 0 1^(d+50) 0^6 1^6 0^6 1^19
 134  7n+14b+28d+8169        1^(n+539) 0 1^2 0^2 1^(b-86) 0^2 1^86 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 135  7n+4565                1^(n+544) 0^2 1^(b-86) 0^2 1^86 0^2 1^(d+50) 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 136  7n+14b+14d+5351        1^(n+547) 0^2 1^(b-84) 0^6 1^82 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 137  7n+7b+4047             1^(n+551) 0 1^2 0 1^(b-86) 0 1^2 0 1^82 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 138  7n+4649                1^(n+556) 0 1^(b-86) 0 1^2 0 1^82 0^6 1^(d+51) 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
```

## Appendix B. TO trip by trip

The rule, for n odd, b even ≥ 82, c odd ≥ 37 and d even ≥ 18:

```
TO:  K(n,2,b,c,d)  -->  K(n+588, b+c-91, d+62, 35, 18)     in 1029n+1001b+987c+882d+458476 steps, 147 trips
```

The rows are read as in Appendix A. Row 0 is K(n,2,b,c,d), and row 147 is K(n+588, b+c-91, d+62, 35, 18).

```
trip  steps of the trip      w (the word after G)
   0  -                      1^n 0 1^2 0 1^2 0 1^b 0^6 1^c 0 1^2 0 1^4 0^6 1^d 0 1^2 0^2 1^2 0 1^3
   1  7n+7b+14c+14d+1149     1^(n+3) 0^9 1^(b-2) 0^2 1^2 0^2 1^(c+3) 0^3 1^2 0^2 1^2 0^2 1^(d+2) 0 1^2 0 1^6 0 1^2
   2  7n+823                 1^(n+7) 0 1^2 0^4 1^(b-2) 0^2 1^2 0^2 1^(c+3) 0^3 1^2 0^2 1^2 0^2 1^(d+2) 0 1^2 0 1^6 0 1^2
   3  7n+841                 1^(n+12) 0^4 1^(b-2) 0^2 1^2 0^2 1^(c+3) 0^3 1^2 0^2 1^2 0^2 1^(d+2) 0 1^2 0 1^6 0 1^2
   4  7n+14b+7c+14d+1226     1^(n+15) 0^2 1^2 0^6 1^(b-6) 0^2 1^(c+6) 0 1^2 0 1^8 0 1^2 0 1^(d+5) 0 1^2
   5  7n+925                 1^(n+19) 0 1^2 0^2 1^2 0 1^(b-6) 0^2 1^(c+6) 0 1^2 0 1^8 0 1^2 0 1^(d+5) 0 1^2
   6  7n+925                 1^(n+24) 0^2 1^2 0 1^(b-6) 0^2 1^(c+6) 0 1^2 0 1^8 0 1^2 0 1^(d+5) 0 1^2
   7  7n+7b+7c+7d+1140       1^(n+27) 0^2 1^(b-2) 0 1^2 0 1^(c+3) 0^6 1^6 0^6 1^(d+5)
   8  7n+7b+971              1^(n+31) 0 1^2 0 1^(b-3) 0 1^(c+3) 0^6 1^6 0^6 1^(d+5)
   9  7n+1009                1^(n+36) 0 1^(b-3) 0 1^(c+3) 0^6 1^6 0^6 1^(d+5)
  10  7n+7b+1017             1^(n+39) 0^3 1^(b+c-2) 0^6 1^6 0^6 1^(d+5)
  11  7n+14b+14c+14d+1307    1^(n+43) 0 1^2 0^2 1^(b+c-3) 0^6 1^4 0^2 1^2 0^2 1^(d+9)
  12  7n+1093                1^(n+48) 0^2 1^(b+c-3) 0^6 1^4 0^2 1^2 0^2 1^(d+9)
  13  7n+14b+14c+14d+1653    1^(n+51) 0^2 1^(b+c-1) 0^6 1^2 0^2 1^4 0^6 1^(d+4) 0^2 1^4 0^6 1^2 0 1^2
  14  7n+7b+7c+1156          1^(n+55) 0 1^2 0 1^(b+c-3) 0 1^2 0 1^2 0^2 1^4 0^6 1^(d+4) 0^2 1^4 0^6 1^2 0 1^2
  15  7n+1177                1^(n+60) 0 1^(b+c-3) 0 1^2 0 1^2 0^2 1^4 0^6 1^(d+4) 0^2 1^4 0^6 1^2 0 1^2
  16  7n+7b+7c+1266          1^(n+63) 0^3 1^(b+c-5) 0^5 1^8 0 1^2 0 1^(d+4) 0^2 1^4 0^6 1^2 0 1^2
  17  7n+14b+14c+28d+2447    1^(n+67) 0 1^2 0^2 1^(b+c-7) 0^2 1^4 0^6 1^8 0 1^2 0 1^(d+2) 0 1^6 0 1^2 0 1^4 0^2 1^4 0 1^2
  18  7n+1261                1^(n+72) 0^2 1^(b+c-7) 0^2 1^4 0^6 1^8 0 1^2 0 1^(d+2) 0 1^6 0 1^2 0 1^4 0^2 1^4 0 1^2
  19  7n+14b+14c+7d+1589     1^(n+75) 0^2 1^(b+c-5) 0^12 1^6 0^6 1^(d) 0^3 1^4 0^6 1^2 0^2 1^8 0 1^2
  20  7n+7b+7c+1296          1^(n+79) 0 1^2 0 1^(b+c-7) 0 1^2 0^7 1^6 0^6 1^(d) 0^3 1^4 0^6 1^2 0^2 1^8 0 1^2
  21  7n+1345                1^(n+84) 0 1^(b+c-7) 0 1^2 0^7 1^6 0^6 1^(d) 0^3 1^4 0^6 1^2 0^2 1^8 0 1^2
  22  7n+7b+7c+1370          1^(n+87) 0^3 1^(b+c-9) 0^2 1^4 0 1^8 0^6 1^(d) 0^3 1^4 0^6 1^2 0^2 1^8 0 1^2
  23  7n+14b+14c+1739        1^(n+91) 0 1^2 0^2 1^(b+c-11) 0^2 1^(d+17) 0^3 1^4 0^6 1^2 0^2 1^8 0 1^2
  24  7n+1429                1^(n+96) 0^2 1^(b+c-11) 0^2 1^(d+17) 0^3 1^4 0^6 1^2 0^2 1^8 0 1^2
  25  7n+14b+14c+14d+1835    1^(n+99) 0^2 1^(b+c-9) 0^6 1^(d+12) 0^2 1^11 0^2 1^8 0 1^2
  26  7n+7b+7c+1436          1^(n+103) 0 1^2 0 1^(b+c-11) 0 1^2 0 1^(d+12) 0^2 1^11 0^2 1^8 0 1^2
  27  7n+1513                1^(n+108) 0 1^(b+c-11) 0 1^2 0 1^(d+12) 0^2 1^11 0^2 1^8 0 1^2
  28  7n+7b+7c+7d+2192       1^(n+111) 0^3 1^(b+c-13) 0^6 1^(d+10) 0^2 1^12 0^2 1^16 0 1^2
  29  7n+14b+14c+28d+2477    1^(n+115) 0 1^2 0^2 1^(b+c-15) 0^2 1^4 0^6 1^(d+21) 0 1^2 0 1^14 0 1^2
  30  7n+1597                1^(n+120) 0^2 1^(b+c-15) 0^2 1^4 0^6 1^(d+21) 0 1^2 0 1^14 0 1^2
  31  7n+14b+14c+7d+1689     1^(n+123) 0^2 1^(b+c-13) 0^12 1^(d+21) 0 1^14 0 1^2
  32  7n+7b+7c+1576          1^(n+127) 0 1^2 0 1^(b+c-15) 0 1^2 0^7 1^(d+21) 0 1^14 0 1^2
  33  7n+1681                1^(n+132) 0 1^(b+c-15) 0 1^2 0^7 1^(d+21) 0 1^14 0 1^2
  34  7n+7b+7c+1650          1^(n+135) 0^3 1^(b+c-17) 0^2 1^4 0 1^(d+23) 0 1^14 0 1^2
  35  7n+14b+14c+21d+3093    1^(n+139) 0 1^2 0^2 1^(b+c-19) 0^2 1^(d+30) 0^2 1^14 0 1^2 0 1^11
  36  7n+1765                1^(n+144) 0^2 1^(b+c-19) 0^2 1^(d+30) 0^2 1^14 0 1^2 0 1^11
  37  7n+14b+14c+14d+2201    1^(n+147) 0^2 1^(b+c-17) 0^6 1^(d+26) 0^6 1^22
  38  7n+7b+7c+1716          1^(n+151) 0 1^2 0 1^(b+c-19) 0 1^2 0 1^(d+26) 0^6 1^22
  39  7n+1849                1^(n+156) 0 1^(b+c-19) 0 1^2 0 1^(d+26) 0^6 1^22
  40  7n+7b+7c+7d+2498       1^(n+159) 0^3 1^(b+c-21) 0^6 1^(d+24) 0^2 1^2 0^2 1^24 0 1^2 0^2 1^2 0 1^3
  41  7n+14b+14c+28d+3003    1^(n+163) 0 1^2 0^2 1^(b+c-23) 0^2 1^4 0^6 1^(d+25) 0 1^2 0 1^22 0 1^2 0 1^2
  42  7n+1933                1^(n+168) 0^2 1^(b+c-23) 0^2 1^4 0^6 1^(d+25) 0 1^2 0 1^22 0 1^2 0 1^2
  43  7n+14b+14c+7d+1941     1^(n+171) 0^2 1^(b+c-21) 0^12 1^(d+25) 0 1^22 0 1^2 0 1^2
  44  7n+7b+7c+1856          1^(n+175) 0 1^2 0 1^(b+c-23) 0 1^2 0^7 1^(d+25) 0 1^22 0 1^2 0 1^2
  45  7n+2017                1^(n+180) 0 1^(b+c-23) 0 1^2 0^7 1^(d+25) 0 1^22 0 1^2 0 1^2
  46  7n+7b+7c+1930          1^(n+183) 0^3 1^(b+c-25) 0^2 1^4 0 1^(d+27) 0 1^22 0 1^2 0 1^2
  47  7n+14b+14c+21d+3865    1^(n+187) 0 1^2 0^2 1^(b+c-27) 0^2 1^(d+34) 0^2 1^22 0 1^2 0 1^2 0 1^2 0 1^10
  48  7n+2101                1^(n+192) 0^2 1^(b+c-27) 0^2 1^(d+34) 0^2 1^22 0 1^2 0 1^2 0 1^2 0 1^10
  49  7n+14b+14c+14d+2593    1^(n+195) 0^2 1^(b+c-25) 0^6 1^(d+30) 0^6 1^21 0 1^2 0 1^10
  50  7n+7b+7c+1996          1^(n+199) 0 1^2 0 1^(b+c-27) 0 1^2 0 1^(d+30) 0^6 1^21 0 1^2 0 1^10
  51  7n+2185                1^(n+204) 0 1^(b+c-27) 0 1^2 0 1^(d+30) 0^6 1^21 0 1^2 0 1^10
  52  7n+7b+7c+7d+2820       1^(n+207) 0^3 1^(b+c-29) 0^6 1^(d+28) 0^2 1^2 0^2 1^24 0^3 1^8 0^2 1^2 0^2 1^4 0 1^2
  53  7n+14b+14c+28d+3925    1^(n+211) 0 1^2 0^2 1^(b+c-31) 0^2 1^4 0^6 1^(d+29) 0 1^2 0 1^20 0^2 1^10 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  54  7n+2269                1^(n+216) 0^2 1^(b+c-31) 0^2 1^4 0^6 1^(d+29) 0 1^2 0 1^20 0^2 1^10 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  55  7n+14b+14c+7d+2193     1^(n+219) 0^2 1^(b+c-29) 0^12 1^(d+29) 0 1^20 0^2 1^10 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  56  7n+7b+7c+2136          1^(n+223) 0 1^2 0 1^(b+c-31) 0 1^2 0^7 1^(d+29) 0 1^20 0^2 1^10 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  57  7n+2353                1^(n+228) 0 1^(b+c-31) 0 1^2 0^7 1^(d+29) 0 1^20 0^2 1^10 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  58  7n+7b+7c+2210          1^(n+231) 0^3 1^(b+c-33) 0^2 1^4 0 1^(d+31) 0 1^20 0^2 1^10 0 1^2 0 1^4 0 1^2 0^3 1^4 0 1^2
  59  7n+14b+14c+21d+4975    1^(n+235) 0 1^2 0^2 1^(b+c-35) 0^2 1^(d+38) 0^2 1^20 0 1^2 0 1^18 0 1^2 0 1^4 0^6 1^6 0 1^2
  60  7n+2437                1^(n+240) 0^2 1^(b+c-35) 0^2 1^(d+38) 0^2 1^20 0 1^2 0 1^18 0 1^2 0 1^4 0^6 1^6 0 1^2
  61  7n+14b+14c+14d+2845    1^(n+243) 0^2 1^(b+c-33) 0^6 1^(d+34) 0^6 1^35 0 1^2 0 1^4 0^6 1^6 0 1^2
  62  7n+7b+7c+2276          1^(n+247) 0 1^2 0 1^(b+c-35) 0 1^2 0 1^(d+34) 0^6 1^35 0 1^2 0 1^4 0^6 1^6 0 1^2
  63  7n+2521                1^(n+252) 0 1^(b+c-35) 0 1^2 0 1^(d+34) 0^6 1^35 0 1^2 0 1^4 0^6 1^6 0 1^2
  64  7n+7b+7c+7d+3424       1^(n+255) 0^3 1^(b+c-37) 0^6 1^(d+32) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^2 1^8 0 1^2 0 1^3
  65  7n+14b+14c+28d+4395    1^(n+259) 0 1^2 0^2 1^(b+c-39) 0^2 1^4 0^6 1^(d+33) 0 1^2 0 1^34 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  66  7n+2605                1^(n+264) 0^2 1^(b+c-39) 0^2 1^4 0^6 1^(d+33) 0 1^2 0 1^34 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  67  7n+14b+14c+7d+2445     1^(n+267) 0^2 1^(b+c-37) 0^12 1^(d+33) 0 1^34 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  68  7n+7b+7c+2416          1^(n+271) 0 1^2 0 1^(b+c-39) 0 1^2 0^7 1^(d+33) 0 1^34 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  69  7n+2689                1^(n+276) 0 1^(b+c-39) 0 1^2 0^7 1^(d+33) 0 1^34 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  70  7n+7b+7c+2490          1^(n+279) 0^3 1^(b+c-41) 0^2 1^4 0 1^(d+35) 0 1^34 0^6 1^6 0^6 1^6 0^2 1^2 0^2 1^4 0 1^2
  71  7n+14b+14c+21d+5311    1^(n+283) 0 1^2 0^2 1^(b+c-43) 0^2 1^(d+42) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  72  7n+2773                1^(n+288) 0^2 1^(b+c-43) 0^2 1^(d+42) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  73  7n+14b+14c+14d+3321    1^(n+291) 0^2 1^(b+c-41) 0^6 1^(d+38) 0^6 1^35 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  74  7n+7b+7c+2556          1^(n+295) 0 1^2 0 1^(b+c-43) 0 1^2 0 1^(d+38) 0^6 1^35 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  75  7n+2857                1^(n+300) 0 1^(b+c-43) 0 1^2 0 1^(d+38) 0^6 1^35 0 1^2 0 1^4 0^6 1^4 0^11 1^4 0 1^2
  76  7n+7b+7c+7d+3814       1^(n+303) 0^3 1^(b+c-45) 0^6 1^(d+36) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^2 1^6 0 1^2 0^2 1^2 0 1^3 0 1^3
  77  7n+14b+14c+28d+4619    1^(n+307) 0 1^2 0^2 1^(b+c-47) 0^2 1^4 0^6 1^(d+37) 0 1^2 0 1^34 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  78  7n+2941                1^(n+312) 0^2 1^(b+c-47) 0^2 1^4 0^6 1^(d+37) 0 1^2 0 1^34 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  79  7n+14b+14c+7d+2697     1^(n+315) 0^2 1^(b+c-45) 0^12 1^(d+37) 0 1^34 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  80  7n+7b+7c+2696          1^(n+319) 0 1^2 0 1^(b+c-47) 0 1^2 0^7 1^(d+37) 0 1^34 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  81  7n+3025                1^(n+324) 0 1^(b+c-47) 0 1^2 0^7 1^(d+37) 0 1^34 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  82  7n+7b+7c+2770          1^(n+327) 0^3 1^(b+c-49) 0^2 1^4 0 1^(d+39) 0 1^34 0^6 1^6 0^6 1^2 0^9 1^2 0 1^2
  83  7n+14b+14c+21d+5463    1^(n+331) 0 1^2 0^2 1^(b+c-51) 0^2 1^(d+46) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  84  7n+3109                1^(n+336) 0^2 1^(b+c-51) 0^2 1^(d+46) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  85  7n+14b+14c+14d+3601    1^(n+339) 0^2 1^(b+c-49) 0^6 1^(d+42) 0^6 1^35 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  86  7n+7b+7c+2836          1^(n+343) 0 1^2 0 1^(b+c-51) 0 1^2 0 1^(d+42) 0^6 1^35 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  87  7n+3193                1^(n+348) 0 1^(b+c-51) 0 1^2 0 1^(d+42) 0^6 1^35 0 1^2 0 1^4 0^7 1^2 0 1^4 0^2 1^2 0^2 1^4 0 1^2
  88  7n+7b+7c+7d+4050       1^(n+351) 0^3 1^(b+c-53) 0^6 1^(d+40) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^3 1^2 0^3 1^2 0^2 1^4 0^6 1^2 0 1^2
  89  7n+14b+14c+28d+5131    1^(n+355) 0 1^2 0^2 1^(b+c-55) 0^2 1^4 0^6 1^(d+41) 0 1^2 0 1^34 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  90  7n+3277                1^(n+360) 0^2 1^(b+c-55) 0^2 1^4 0^6 1^(d+41) 0 1^2 0 1^34 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  91  7n+14b+14c+7d+2949     1^(n+363) 0^2 1^(b+c-53) 0^12 1^(d+41) 0 1^34 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  92  7n+7b+7c+2976          1^(n+367) 0 1^2 0 1^(b+c-55) 0 1^2 0^7 1^(d+41) 0 1^34 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  93  7n+3361                1^(n+372) 0 1^(b+c-55) 0 1^2 0^7 1^(d+41) 0 1^34 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  94  7n+7b+7c+3050          1^(n+375) 0^3 1^(b+c-57) 0^2 1^4 0 1^(d+43) 0 1^34 0^6 1^6 0^6 1^9 0 1^2 0 1^2
  95  7n+14b+14c+21d+5845    1^(n+379) 0 1^2 0^2 1^(b+c-59) 0^2 1^(d+50) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^9 0 1^3
  96  7n+3445                1^(n+384) 0^2 1^(b+c-59) 0^2 1^(d+50) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^9 0 1^3
  97  7n+14b+14c+14d+3881    1^(n+387) 0^2 1^(b+c-57) 0^6 1^(d+46) 0^6 1^35 0 1^2 0 1^4 0^6 1^9 0 1^3
  98  7n+7b+7c+3116          1^(n+391) 0 1^2 0 1^(b+c-59) 0 1^2 0 1^(d+46) 0^6 1^35 0 1^2 0 1^4 0^6 1^9 0 1^3
  99  7n+3529                1^(n+396) 0 1^(b+c-59) 0 1^2 0 1^(d+46) 0^6 1^35 0 1^2 0 1^4 0^6 1^9 0 1^3
 100  7n+7b+7c+7d+4344       1^(n+399) 0^3 1^(b+c-61) 0^6 1^(d+44) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^2 1^14 0 1^2
 101  7n+14b+14c+28d+5455    1^(n+403) 0 1^2 0^2 1^(b+c-63) 0^2 1^4 0^6 1^(d+45) 0 1^2 0 1^34 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
 102  7n+3613                1^(n+408) 0^2 1^(b+c-63) 0^2 1^4 0^6 1^(d+45) 0 1^2 0 1^34 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
 103  7n+14b+14c+7d+3201     1^(n+411) 0^2 1^(b+c-61) 0^12 1^(d+45) 0 1^34 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
 104  7n+7b+7c+3256          1^(n+415) 0 1^2 0 1^(b+c-63) 0 1^2 0^7 1^(d+45) 0 1^34 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
 105  7n+3697                1^(n+420) 0 1^(b+c-63) 0 1^2 0^7 1^(d+45) 0 1^34 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
 106  7n+7b+7c+3330          1^(n+423) 0^3 1^(b+c-65) 0^2 1^4 0 1^(d+47) 0 1^34 0^6 1^6 0^6 1^10 0^2 1^4 0 1^2
 107  7n+14b+14c+21d+6329    1^(n+427) 0 1^2 0^2 1^(b+c-67) 0^2 1^(d+54) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 108  7n+3781                1^(n+432) 0^2 1^(b+c-67) 0^2 1^(d+54) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 109  7n+14b+14c+14d+4161    1^(n+435) 0^2 1^(b+c-65) 0^6 1^(d+50) 0^6 1^35 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 110  7n+7b+7c+3396          1^(n+439) 0 1^2 0 1^(b+c-67) 0 1^2 0 1^(d+50) 0^6 1^35 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 111  7n+3865                1^(n+444) 0 1^(b+c-67) 0 1^2 0 1^(d+50) 0^6 1^35 0 1^2 0 1^4 0^6 1^8 0^3 1^6 0 1^2
 112  7n+7b+7c+7d+4884       1^(n+447) 0^3 1^(b+c-69) 0^6 1^(d+48) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^2 1^10 0 1^2 0 1^6 0^2 1^2 0^2 1^4 0 1^2
 113  7n+14b+14c+28d+5737    1^(n+451) 0 1^2 0^2 1^(b+c-71) 0^2 1^4 0^6 1^(d+49) 0 1^2 0 1^34 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 114  7n+3949                1^(n+456) 0^2 1^(b+c-71) 0^2 1^4 0^6 1^(d+49) 0 1^2 0 1^34 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 115  7n+14b+14c+7d+3453     1^(n+459) 0^2 1^(b+c-69) 0^12 1^(d+49) 0 1^34 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 116  7n+7b+7c+3536          1^(n+463) 0 1^2 0 1^(b+c-71) 0 1^2 0^7 1^(d+49) 0 1^34 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 117  7n+4033                1^(n+468) 0 1^(b+c-71) 0 1^2 0^7 1^(d+49) 0 1^34 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 118  7n+7b+7c+3610          1^(n+471) 0^3 1^(b+c-73) 0^2 1^4 0 1^(d+51) 0 1^34 0^6 1^6 0^6 1^12 0 1^2 0^2 1^2 0 1^3
 119  7n+14b+14c+21d+6647    1^(n+475) 0 1^2 0^2 1^(b+c-75) 0^2 1^(d+58) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 120  7n+4117                1^(n+480) 0^2 1^(b+c-75) 0^2 1^(d+58) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 121  7n+14b+14c+14d+4441    1^(n+483) 0^2 1^(b+c-73) 0^6 1^(d+54) 0^6 1^35 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 122  7n+7b+7c+3676          1^(n+487) 0 1^2 0 1^(b+c-75) 0 1^2 0 1^(d+54) 0^6 1^35 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 123  7n+4201                1^(n+492) 0 1^(b+c-75) 0 1^2 0 1^(d+54) 0^6 1^35 0 1^2 0 1^4 0^6 1^10 0^3 1^4 0^2 1^4 0 1^2
 124  7n+7b+7c+7d+5102       1^(n+495) 0^3 1^(b+c-77) 0^6 1^(d+52) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^2 1^12 0 1^2 0 1^5 0 1^3
 125  7n+14b+14c+28d+6083    1^(n+499) 0 1^2 0^2 1^(b+c-79) 0^2 1^4 0^6 1^(d+53) 0 1^2 0 1^34 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 126  7n+4285                1^(n+504) 0^2 1^(b+c-79) 0^2 1^4 0^6 1^(d+53) 0 1^2 0 1^34 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 127  7n+14b+14c+7d+3705     1^(n+507) 0^2 1^(b+c-77) 0^12 1^(d+53) 0 1^34 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 128  7n+7b+7c+3816          1^(n+511) 0 1^2 0 1^(b+c-79) 0 1^2 0^7 1^(d+53) 0 1^34 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 129  7n+4369                1^(n+516) 0 1^(b+c-79) 0 1^2 0^7 1^(d+53) 0 1^34 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 130  7n+7b+7c+3890          1^(n+519) 0^3 1^(b+c-81) 0^2 1^4 0 1^(d+55) 0 1^34 0^6 1^6 0^6 1^12 0^3 1^2 0 1^2
 131  7n+14b+14c+21d+7057    1^(n+523) 0 1^2 0^2 1^(b+c-83) 0^2 1^(d+62) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 132  7n+4453                1^(n+528) 0^2 1^(b+c-83) 0^2 1^(d+62) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 133  7n+14b+14c+14d+4721    1^(n+531) 0^2 1^(b+c-81) 0^6 1^(d+58) 0^6 1^35 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 134  7n+7b+7c+3956          1^(n+535) 0 1^2 0 1^(b+c-83) 0 1^2 0 1^(d+58) 0^6 1^35 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 135  7n+4537                1^(n+540) 0 1^(b+c-83) 0 1^2 0 1^(d+58) 0^6 1^35 0 1^2 0 1^4 0^6 1^10 0^2 1^6 0 1^2 0 1^3
 136  7n+7b+7c+7d+5500       1^(n+543) 0^3 1^(b+c-85) 0^6 1^(d+56) 0^2 1^2 0^2 1^38 0^3 1^2 0^2 1^2 0^2 1^12 0 1^2 0 1^10 0 1^2
 137  7n+14b+14c+28d+6429    1^(n+547) 0 1^2 0^2 1^(b+c-87) 0^2 1^4 0^6 1^(d+57) 0 1^2 0 1^34 0^6 1^6 0^6 1^19
 138  7n+4621                1^(n+552) 0^2 1^(b+c-87) 0^2 1^4 0^6 1^(d+57) 0 1^2 0 1^34 0^6 1^6 0^6 1^19
 139  7n+14b+14c+7d+3957     1^(n+555) 0^2 1^(b+c-85) 0^12 1^(d+57) 0 1^34 0^6 1^6 0^6 1^19
 140  7n+7b+7c+4096          1^(n+559) 0 1^2 0 1^(b+c-87) 0 1^2 0^7 1^(d+57) 0 1^34 0^6 1^6 0^6 1^19
 141  7n+4705                1^(n+564) 0 1^(b+c-87) 0 1^2 0^7 1^(d+57) 0 1^34 0^6 1^6 0^6 1^19
 142  7n+7b+7c+4170          1^(n+567) 0^3 1^(b+c-89) 0^2 1^4 0 1^(d+59) 0 1^34 0^6 1^6 0^6 1^19
 143  7n+14b+14c+21d+7455    1^(n+571) 0 1^2 0^2 1^(b+c-91) 0^2 1^(d+66) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 144  7n+4789                1^(n+576) 0^2 1^(b+c-91) 0^2 1^(d+66) 0^2 1^34 0 1^2 0 1^4 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 145  7n+14b+14c+14d+5001    1^(n+579) 0^2 1^(b+c-89) 0^6 1^(d+62) 0^6 1^35 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 146  7n+7b+7c+4236          1^(n+583) 0 1^2 0 1^(b+c-91) 0 1^2 0 1^(d+62) 0^6 1^35 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
 147  7n+4873                1^(n+588) 0 1^(b+c-91) 0 1^2 0 1^(d+62) 0^6 1^35 0 1^2 0 1^4 0^6 1^18 0 1^2 0^2 1^2 0 1^3
```

AI assistance: Claude (Anthropic) assisted with the original formal proofs, proof sketches, scripts and checks. GPT-6 Astra (OpenAI) assisted with independent audit and submission preparation.
