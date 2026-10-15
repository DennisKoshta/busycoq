# 1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---: never halts

The head bounces between a binary counter and a row of blocks. Each counter overflow creates a moving front, and the block counts evolve by one of two affine rules.

A single hexagonal invariant works for both rules, so predicting their parity sequence is unnecessary.

This machine appears in dyuan01's October 1 longitudinal-filter list. The proof below uses direct window lemmas and an arithmetic invariant.

It builds on the moving particles and counter digits of busycoq's `SBCv7.v`, Module TM4.

**Summary.** The left end of the tape is a binary counter. To its right is a row of 5-cell blocks. The head bounces between the counter and the right edge, adding 1 to the counter on every visit to it.

- **P phase.** Each bounce adds one `B` block at the right edge.

- **Overflow.** When the counter overflows, it gains a digit and a 3-cell marker, the *front* `111`, appears at its right.

- **Q phase.** The front walks right two blocks every three bounces.

- **Conversion.** When the front reaches the `B` blocks, it turns them all into `A` blocks.

Each full cycle doubles the counter range. The block counts after a cycle are an affine function of the counts before it, and the function has two branches, chosen by the parity of a count.

The proof derives exact macro rules for the right-edge visits (§3), and then finds a hexagon in the scaled block counts that both branches map into itself (§4).

Since both branches preserve it, the parity sequence never has to be predicted.

## 1. Notation and families

Tapes are written in directed-head notation. `L <S R` means the head is in state S on the last cell of L. `L S> R` means the head is in state S on the first cell of R.

| word | meaning |
|---|---|
| `C_k(n)` | n in k binary digits, MSB first, digit 1 = `1010`, digit 0 = `0010` (requires 2^(k-1) ≤ n < 2^k) |
| `A = 00111`, `B = 10111`, front `111` | blocks as they look **left** of the head ("left form") |
| `A' = 00101`, `B' = 00001` | the same blocks **right** of a moving head ("right form") |
| `<A 001`, `001 E>` | the moving head. It always carries the 3 cells `001` (TM4's `hL = (A,[0;0;1])`, `hR = (E,<[0;0;1])`) |

The families below are the right-edge visits in state C. By direct simulation to step 1e9, 4,711 of the 4,722 such visits have one of these two shapes;

the other 11 are the start and mid-conversion visits.

```
P(k,n,X,z)   := 0^inf C_k(n) A^X B^z 00 C> 0^inf                 X,z >= 0
Q(k,n,x,y,z) := 0^inf C_k(n) A^x 111 A^y B^z 00 C> 0^inf         x >= 1; y,z >= 0
```

## 2. Rule table (busycoq comment-block style)

```
1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---

C_k(n): n in k bits MSB first, 1 -> 1010, 0 -> 0010;   A = 00111, B = 10111
P(k,n,X,z)   := 0^inf C_k(n) A^X B^z 00 C> 0^inf
Q(k,n,x,y,z) := 0^inf C_k(n) A^x 111 A^y B^z 00 C> 0^inf                    (x >= 1)

R1  P(k,n,X,z)      --> P(k,n+1,X,z+1)                     n+1 <= 2^k-1
R2  P(k,2^k-1,X,z)  --> Q(k+1,2^k+1,1,X-2,z+1)             X >= 2
R3  Q(k,n,x,y+2,z)  --> Q(k,n+3,x+2,y,z+1)                 n+3 <= 2^k-1
R4  Q(k,n,x,0,z)    --> P(k,n+z+2,x+z+1,0)                 n+z+2  <= 2^k-1
R5  Q(k,n,x,1,z)    --> P(k,n+2z+7,x+z+4,0)                n+2z+7 <= 2^k-1
R5o Q(k,n,x,1,z)    --> Q(k+1,2^k+1+3m,1+2m,x+z+2-2m,0)    m := n+2z+7-2^k >= 0,  x+z+2-2m >= 1,  3m <= 2^k-2

remark (true, never used): R4o Q(k,n,x,0,z) --> Q(k+1,2^k+1+3m,1+2m,x+z-1-2m,0),
                           m := n+z+2-2^k >= 0, x+z-1-2m >= 1, 3m <= 2^k-2

steps: R1 32X+32z+16t(n)+47,  R2 32X+32z+16k+61,  R3 96x+32y+32z+16(t(n)+t(n+1)+t(n+2))+197
       (t(n) = number of trailing 1 bits of n)

cycle (N = 2^k):  S(k,Y,Z) := Q(k+1, N+1+3m, 1+2m, Y-2m, Z+m),  m = max(0,-Z)
  (S(k,.) is the first right-edge visit after the counter grows to k+1 digits; its counter
   lies in [N,2N) and overflows at 2N)
  S(k,2j,Z)   -->+ S(k+1, 3j+Z,   N-3-4j-Z)      via R3^(j-m), R4, R1^(N-4-2Y-Z), R2
  S(k,2j+1,Z) -->+ S(k+1, 3j+3+Z, N-8-5j-2Z)     via R3^(j-m), then R5, R1^*, R2  or  R5o
invariant (N >= 64):  8Y >= N, 8Y <= 3N, 3Z <= N, 8Z >= -N, 4Y+2Z >= N, 20Y+16Z <= 9N
start: c0 -->(17215) S(6,16,0) = Q(7,65,1,16,0)
```

Every case is covered. For P: n < 2^k-1 uses R1, and n = 2^k-1 uses R2 (X ≥ 2 holds; see §4). For Q: y ≥ 2 uses R3. y = 0 uses R4: on the invariant the counter never overflows during an even conversion (§4), so R4o is never needed.

y = 1 uses R5 if the counter does not overflow during the conversion, and R5o if it does. The domain conditions that the run must satisfy (no overflow inside a Q phase, R2's X ≥ 2, no overflow in an even conversion, and the R5o conditions) are exactly what the invariant in §4 guarantees.

The conditions matter: on each of 677 small out-of-domain instances, the overflow chain of §3.3 does not apply, and the out-of-domain configuration `Q(4,8,400,0,180)` halts (after 327,891 steps).

This shows the conditions matter, not that they are necessary; the domain of R5o is a sufficient condition chosen for the cycle lemma.

## 3. Proofs of the rules

### 3.1 Shift rules (level 0)

Each rule below is a fixed finite run. In the .v, each is a lemma of the same name, proved by `es`. Rules marked `0^inf` need blank tape on that side.

All others hold for every context.

| rule | statement | steps |
|---|---|---|
| ENDL | `00 C> 0^inf  →  <A 001 0^inf` | 7 |
| AL | `00111 <A 001  →  <A 001 00101` | 25 |
| BL | `10111 <A 001  →  <A 001 00001` | 9 |
| AR | `001 E> 00101  →  00111 001 E>` | 7 |
| BR | `001 E> 00001  →  10111 001 E>` | 23 |
| ENDR | `001 E> 0^inf  →  10111 00 C> 0^inf` | 22 |
| D1L | `1010 <A 001  →  <A 001 0101` (carry through a 1 digit) | 12 |
| FLIP | `0010 <A 001  →  1010 001 E>` (0 digit becomes 1; turn) | 18 |
| D0R | `001 E> 0101  →  0010 001 E>` (carried digit restored as 0) | 4 |
| OVL | `0^inf <A 001 01  →  0^inf 1010 001 E>` (counter overflow) | 12 |
| OVR | `001 E> 01 00101  →  0010 <A 001 101` (new digit and new front) | 10 |
| FL | `00111 111 <A 001  →  <A 001 001 00001` (front, leftward) | 28 |
| FR1 | `001 E> 001 00001  →  00111 <A 001 001` | 13 |
| FR2 | `001 E> 001 00101  →  00111 <A 001 101` | 13 |
| FR3 | `001 E> 101 00101  →  00111 111 001 E>` (front passes) | 10 |
| FR4 | `001 E> 101 00001  →  <A 001 001 00101` | 36 |
| FE0 | `001 E> 001 0^inf  →  00111 00 C> 0^inf` | 6 |
| FE1 | `001 E> 101 0^inf  →  <A 001 001 001 0^inf` | 36 |
| FE2 | `001 E> 001 001 0^inf  →  00111 <A 001 1 0^inf` | 13 |
| FE3 | `001 E> 1 0^inf  →  <A 001 0011 0^inf` | 36 |
| FE4 | `001 E> 0011 0^inf  →  00111 <A 001 001 0^inf` | 25 |

### 3.2 Repeated rules (level 1)

- `AL^a: A^a <A 001 → <A 001 A'^a` (25a steps). Likewise `BL^z` (9z), `AR^a: 001 E> A'^a → A^a 001 E>` (7a), `BR^z` (23z), `D1L^t`, and `D0R^t`.

- **CTR.** For n+1 ≤ 2^k-1: `0^inf C_k(n) <A 001 → 0^inf C_k(n+1) 001 E>` in 16t(n)+18 steps. Write `C_k(n) = W 0010 1010^t`.

Then:

  - `D1L^t` gives `W 0010 <A 001 0101^t`;

  - `FLIP` gives `W 1010 001 E> 0101^t`;

  - `D0R^t` gives `W 1010 0010^t 001 E> = C_k(n+1) 001 E>`.

- **OV.** `0^inf C_k(2^k-1) <A 001 A' A' → 0^inf C_{k+1}(2^k+1) A 111 001 E>` in 16k+46 steps:

  - `D1L^k` gives `0^inf <A 001 0101^k A' A'`, which is the same tape as `0^inf <A 001 01 0101^(k-1) 01 00101 00101`;

  - `OVL` gives `0^inf 1010 001 E> 0101^(k-1) 01 00101 00101`;

  - `D0R^(k-1)` gives `0^inf 1010 0010^(k-1) 001 E> 01 00101 00101`;

  - `OVR` gives `0^inf C_{k+1}(2^k) <A 001 101 00101`;

  - `FLIP` (that is, CTR with t = 0) gives `0^inf C_{k+1}(2^k+1) 001 E> 101 00101`;

  - `FR3` finishes.

  The counter gains a digit: 2 of its 4 cells come from the blank left side and 2 from the right. The 13 cells `001 A' A'` become the 11 cells `A 111 001`, which are the new front.

- **QC (one front step).** For every right word G, with x ≥ 1, y ≥ 2, and n+3 ≤ 2^k-1:

  ```
  C_k(n) A^x 111 A^y <A 001 G
  -AL^y->                         C_k(n) A^x 111 <A 001 A'^y G
  -FL->                           C_k(n) A^(x-1) <A 001 001 B' A'^y G          front now "001 B'"
  -AL^(x-1),CTR,AR^(x-1),FR1->    C_k(n+1) A^x <A 001 001 A'^y G               front "001"
  -AL^x,CTR,AR^x,FR2->            C_k(n+2) A^(x+1) <A 001 101 A'^(y-1) G       front "101"
  -AL^(x+1),CTR,AR^(x+1),FR3->    C_k(n+3) A^(x+2) 111 001 E> A'^(y-2) G       front back in left form
  -AR^(y-2)->                     C_k(n+3) A^(x+2) 111 A^(y-2) 001 E> G
  ```

  So the front is a 3-state gadget: it reflects the head twice, lets it through on the third visit, and ends up two blocks further right.

### 3.3 Macro rules

- **R1** is `ENDL, BL^z, AL^X, CTR, AR^X, BR^z, ENDR`. The step count is 7+9z+25X+(16t+18)+7X+23z+22.

- **R2** is `ENDL, BL^z, AL^X, OV, AR^(X-2), BR^z, ENDR`. It needs X ≥ 2, because OV uses two A' blocks.

- **R3** is `ENDL, BL^z, QC (with G = B'^z 0^inf), BR^z, ENDR`.

**Conversion (R4, R5, R5o; R4o as a remark).** The derivation below treats both parities at once, because the argument is the same.

The proof only needs the overflow case for y = 1 (R5o): §4 shows that on the invariant an even conversion never overflows.

Start from `Q(k,n,x,y,z)` with y ∈ {0,1}. Applying `ENDL, BL^z, AL^y, FL` gives `0^inf C_k(n) A^(x-1) <A 001 G_1`, where the old front plus the B blocks now form a gadget:

- even (y=0): `G_1 = 001 B'^(z+1) 0^inf`. Its hits are `FR1` z+1 times, then `FE0`.

- odd (y=1): `G_1 = 001 B' A' B'^z 0^inf`. Its hits are `FR1, FR2, (FR4, FR2)^z, FE1, FE2, FE3, FE4, FE0`. The gadget word runs through `001 B' A' B'^z`, `001 A' B'^z`, `101 B'^z`, `001 A' B'^(z-1)`, `101 B'^(z-1)`, …, `101`, `001 001`, `1`, `0011`, `001`, and then the right edge.

So there are T = z+2 (even) or 2z+7 (odd) hits. Every hit except the last is a reflection `001 E> G_t → A^(δ_t) <A 001 G_(t+1)`.

Here δ_t = 1 for FR1, FR2, FE2 and FE4, and δ_t = 0 for FR4, FE1 and FE3. The last hit, `FE0`, ends at the right edge and adds one more A;

count it as δ_T = 1. In total, Σ_t δ_t = z+2 (even) or z+5 (odd).

- **Round without overflow** (n+1 ≤ 2^k-1): `C_k(n) A^a <A 001 G_t` goes by `AL^a, CTR, AR^a, hit_t` to `C_k(n+1) A^(a+δ_t) <A 001 G_(t+1)`.

Starting from a_1 = x-1:

  - **R4/R5.** If all T rounds avoid overflow (n+T ≤ 2^k-1), the run ends at `P(k, n+T, x-1+Σδ, 0)`, which is R4 or R5.

- **R5o (and R4o).** Otherwise the counter overflows in round r = 2^k-n ≤ T, and m := T-r rounds remain after that.

  - **Rounds 1..r-1** are no-overflow rounds as above: by the choice of r, each one starts with counter ≤ 2^k-2.

  - **Round r** is `AL^a, OV, AR^(a-2), hit_r` with a = a_r = x-1+Σ_{t<r}δ_t. OV needs the two A' blocks right of the head, so a_r ≥ 2. If m ≥ 1, round r ends at `C_{k+1}(2^k+1) A 111 A^(b) <A 001 G_(r+1)` with b = b_(r+1) := a_r-2+δ_r A blocks between the two fronts.

A new front has started next to the counter while the old gadget is still converting.

  - **Each later round s** (r < s ≤ T) is `QC, hit_s`. QC needs b_s ≥ 2. The new front moves 2 blocks right, the counter gains 3, and the between-count becomes b_(s+1) = b_s-2+δ_s ≤ b_s-1.

  - **End.** The last hit is FE0 (δ_T = 1), which gives `Q(k+1, 2^k+1+3m, 1+2m, y_f, 0)` with y_f = (x-1+Σ_{t<r}δ_t) - 2 + Σ_{t≥r}δ_t - 2m = x-3+Σδ-2m.

This is x+z+2-2m (odd, R5o) or x+z-1-2m (even, R4o).

  - **Domain.** Assume y_f ≥ 1 and 3m ≤ 2^k-2.

    - If m = 0, round r is the last round and its hit is FE0, so it ends at `Q(k+1, 2^k+1, 1, a_r-1, 0)`. Then y_f = a_r-1, and y_f ≥ 1 gives a_r ≥ 2 directly.

There are no QC rounds. (The initial segment's last step, which reaches S(6,16,0), is this case; see §5.)

    - If m ≥ 1, the last round T is a QC round and y_f = b_T-2+1, so b_T = y_f+1 ≥ 2. The between-counts strictly decrease, so b_s ≥ b_T ≥ 2 for every r < s ≤ T, which is what each QC needs.

Also b_(r+1) ≥ b_T ≥ 2 gives a_r = b_(r+1)+2-δ_r ≥ 3.

    - The counter fits in k+1 bits: the last QC starts at 2^k+1+3(m-1) and needs that value plus 3 to be ≤ 2^(k+1)-1, that is, 3m ≤ 2^k-2.

## 4. Coverage, invariant, progress

**Cycle states.** Let N = 2^k and m = max(0,-Z). Define `S(k,Y,Z) := Q(k+1, N+1+3m, 1+2m, Y-2m, Z+m)`. S(k,·) is the first right-edge visit after the counter grows to k+1 digits: its counter lies in [N,2N) and overflows at 2N.

(So S's index k is one less than the Q/P level k+1; in the cycle lemma, the next overflow is at 2N and the next cycle state is S(k+1,·) at level k+2.)

- For Z ≥ 1 this is R2's output `Q(k+1,N+1,1,Y,Z)`.

- For Z ≤ 0 it is R5o's output, written as if those m front steps had been R3 steps from x = 1.

**Cycle lemma.** Write F_N(Y,Z) = (Y',Z') for the two branches in §2. Suppose that:

- (a) Y+2Z ≥ 1;

- (b) 3⌊Y/2⌋ ≤ N-2;

- (c) Y' ≥ 0, Y'+2Z' ≥ 1 and 3⌊Y'/2⌋ ≤ 2N-2;

- (d) if Y is even, then Z' ≥ 1 (equivalently 2Y+Z ≤ N-4).

Then S(k,Y,Z) →+ S(k+1,Y',Z').

*Proof.* Let p = Y mod 2 and j = ⌊Y/2⌋. By (a), j ≥ m.

- **Q phase.** `R3^(j-m)` gives `Q(k+1, n, x, p, z)` with n = N+1+3j, x = 1+2j and z = Z+j ≥ 0. No overflow occurs, by (b).

- **Conversion.** Let T = z+2 (even) or 2z+7 (odd), and s = n+T. In both cases Z' = 2N-s (see the formula below).

  - If s ≤ 2N-1: R4/R5 gives `P(k+1, s, X, 0)`, then `R1^(2N-1-s)` gives `P(k+1, 2N-1, X, 2N-1-s)`, and R2 gives `S(k+1, X-2, 2N-s)`.

R2's condition X ≥ 2 is Y' ≥ 0. For even Y this case always applies, since s = 2N-Z' ≤ 2N-1 by (d): the even branch is R4, R1^(N-4-2Y-Z), R2.

  - If s ≥ 2N, then Y is odd by (d), and R5o with m' = s-2N gives `S(k+1, X-2, 2N-s)` directly. Its conditions are y_f = Y'+2Z' ≥ 1, and 3m' ≤ 3⌊Y'/2⌋ ≤ 2N-2, where m' ≤ ⌊Y'/2⌋ because Y' ≥ 2m'+1. Both come from (c).

- **The formula.** In both cases (Y',Z') = (X-2, 2N-s):

  - even: X-2 = x+z-1 = 3j+Z, and 2N-s = N-3-4j-Z;

  - odd: X-2 = x+z+2 = 3j+3+Z, and 2N-s = N-8-5j-2Z. ∎

**Invariant.** Let R_N be the integer points (Y,Z) with

`8Y ≥ N,  8Y ≤ 3N,  3Z ≤ N,  8Z ≥ -N,  4Y+2Z ≥ N,  20Y+16Z ≤ 9N`.

In u = Y/N and v = Z/N this is the hexagon R with vertices (1/8,1/4), (1/8,1/3), (11/60,1/3), (3/8,3/32), (3/8,-1/8) and (5/16,-1/8).

For N ≥ 64:

- **(i) R_N gives (a), (b) and (d).** On R, u+2v ≥ 1/16, so Y+2Z ≥ N/16 ≥ 4. Also 3⌊Y/2⌋ ≤ (3/2)(3/8)N = 9N/16 ≤ N-2. For (d): 16(2Y+Z) = (20Y+16Z) + 12Y ≤ 9N + 12·3N/8, so 2Y+Z ≤ 27N/32 (on R, max 2u+v = 27/32, at vertex (3/8,3/32)).

Then 2Y+Z ≤ N-4 for N ≥ 26. So on the invariant the even branch always takes R4, then R1^(N-4-2Y-Z), then R2, and Z' = N-3-2Y-Z ≥ 5N/32-3 > 0. The counter never overflows during an even conversion, and R4o is never used.

- **(ii) F_N maps R_N into R_2N.** With u' = Y'/2N and v' = Z'/2N, each branch is affine in (u,v):

  - even: u' = 3u/4 + v/2 and v' = 1/2 - u - v/2 - 3/(2N);

  - odd: u' = 3u/4 + v/2 + 3/(4N) and v' = 1/2 - 5u/4 - v - 11/(4N).

  An affine map sends the hexagon into itself if it sends the 6 vertices in. The image coordinates are affine in 1/N ∈ (0,1/64], so checking 1/N = 0 and 1/N = 1/64 covers every N ≥ 64. All 6 vertices × 2 branches × 2 values × 6 facets hold, with slack at least 3/128 in the integer-coefficient form above (checked in exact rational arithmetic).

The minimum is attained by the odd images of the edge u = 1/8 against the facet 4Y+2Z ≥ N, at 1/N = 1/64. For the odd branch that slack is 4u'+2v'-1 = u/2 - 5/(2N), which does not depend on v, so both vertices (1/8,1/4) and (1/8,1/3) tie at 1/16 - 5/128 = 3/128.

- **(i) and (ii) give (c).** Applying (i) at level 2N to the image point gives (c), and Y' ≥ 2N/8 > 0.

The two linear parts have spectral radius below 1: the even eigenvalues have modulus sqrt(2)/4 (approximately 0.354), and the odd eigenvalues are 1/4 and -1/2. As N tends to infinity, the two affine maps tend to maps with fixed points (2/7,1/7) and (2/9,1/9).

**Parity.** The branch at each level is the parity of Y, which behaves like a pseudo-random bit; in the real run, starting at k = 4, the sequence is even, odd, even, even, odd, odd, even, ….

But R is mapped into itself by **both** branches, so the proof never needs to know the parities, and nonhalting does not depend on them.

**Progress.** Every macro rule contains ENDL (7 steps), so each cycle takes at least 1 step; in fact it takes Θ(4^k).

**Conclusion.** The run reaches S(6,16,0), which is in R_64 (the facet 4Y+2Z ≥ N is tight there: 64 = 64). By induction, for every k ≥ 6, the run reaches S(k+1,F(Y,Z)) from S(k,Y,Z), with the invariant holding at each level.

So the machine runs forever.

**Why F1 is never reached.** Every step of the run lies inside one application of the 21 shift rules of §3.1, and each of those is an exact finite run (one `es` lemma in the .v).

F is entered only by E1 = 1RF. That happens only inside FR3, FR4, FE1 and FE3, where E reads the 1 of a front word `101` or the lone `1` of FE3. Each time, the next cell is 0, so F0 = 1RC runs and F1 (halt) never does.

## 5. Initial segment

`c0 = 0^inf A> 0^inf` reaches `Q(5,17,1,2,2) = S(4,2,2)` in 1,507 steps, by direct simulation (exact). From there the rules give:

- `R3` to `Q(5,20,3,0,3)` (step 1,912);

- `R4` to `P(5,25,7,0)` (step 2,826);

- `R1^6` to `P(5,31,7,6)` (step 4,996);

- `R2` to `Q(6,33,1,5,7) = S(5,5,7)` (step 5,553);

- `R3^2` to `Q(6,39,5,1,9)` (step 7,003);

- `R5o` with m = 0 to `Q(7,65,1,16,0) = S(6,16,0)` (step 17,215). Here the overflow round is the last round (its hit is FE0), the case m = 0 of the R5o domain in §3.3.

Direct simulation also gives `c0 -->(17215) Q(7,65,1,16,0)`. In the .v this is `init0 : c0 -->* 0inf <* d1 <* d0^^5 <* d1 <* bA <* <[1;1;1] <* bA^^16 <* <[0;0] {{C}}> 0inf`, proved by `esx`, and `init : c0 -->* CfgF 5 0 16 0` follows from it by `apply init0` (conversion computes `ctr 7 65`).

So the .v goes straight to S(6,16,0); the rule-by-rule path from step 1,507 above is a cross-check only. The induction starts at k = 6 (N = 64), because S(4,…) and S(5,…) are below the N ≥ 64 bound of the invariant.

Check against the real run: starting from step 1,507, applying only these rules reproduces 36 configurations of the direct simulation from that point on, each the first or last configuration of a P or Q phase, with the exact step number, up to `P(15,25768,7028,0)` at step 2,318,632,923. The run's cycle states (k,Y,Z) are (6,16,0), (7,24,29), (8,65,48), (9,147,-8), (10,214,155), (11,476,438), (12,1152,655), (13,2383,1134) and (14,4710,-39), all inside R.

## 6. Mapping to busycoq, and what is new

**Templates.** `verify/SBCv7.v` has six solved machines that differ from this one only in F0:

| Module | F0 |
|---|---|
| TM1 | `0LC` |
| TM2 | `0RD` |
| TM3 | `0LA` |
| TM4 | `0RA` |
| TM18 | `0LD` |
| TM37 | `1RB` |

Other files have more. `IndSBCv1` proves `nonhalt42` with F0 = `1RA`.

`CTLv1` proves `nonhalt22216` and `nonhalt22724` with F0 = `0LB` and `1LA`. Those are decider certificates, not readable templates.

TM1–TM4 share the moving-head notations and the two counter digits:

```
hR = (E,<[0;0;1])
hL = (A,[0;0;1])
d0, d1
```

They also share the lemma list from `LIncs` through `BigStep` and `nonhalt`. TM18 adds a second particle pair, `hR'` and `hL'`, while TM37 uses different particles. TM4 supplies the names here; TM1–TM3 would serve equally well.

**TM4 in brief.** TM4 uses the Longitudinal library, with segments `segRLs` and `sideRLs`. Its counter is handled by `LIncs` via `BC.Mul2` and `BC.Incs` on `tm'`.

Its digits are our 0010 and 1010:

```
d0 = <[0;0;1;0]
d1 = <[1;0;1;0]
```

Its right side is a unary counter, `UC1.Incs` on `w0/w1/w0'/w1'`. TM4 has one `BigStep` per counter overflow, followed by `progress_nonhalt_cond` with the invariant below:

```
Rn ls <= (2^k-1)*2
```

**What carries over:**

- the particles: TM4's `hR`/`hL` are our `001 E>`/`<A 001`;

- the digits;

- the counter behaviour: D1L, FLIP, D0R, OVL and OVR never enter F, so CTR and OV up to its final FR3 hold verbatim for TM4's machine;

- the overall shape: init, then `progress_nonhalt_cond` with a linear invariant.

**What is new:**

- **Blocks.** Our F0 = 1RC changes every right-side word. The blocks are `00111`/`00101` and `10111`/`00001`, not TM4's.

- **Front gadget.** A 3-state front gadget (FL, FR1, FR2, FR3) walks right inside the block row.

- **Conversion gadget.** It has a parity split: even uses FR1 only; odd uses FR1, FR2, (FR4, FR2)^z, then FE1–FE4.

- **Overflow during an odd conversion (R5o).** The new front's QC rounds run interleaved with the old gadget's hits (`PostOV`, `ConvOV`).

This is the main new lemma. Only the odd case is used: on the invariant an even conversion never overflows (§4).

- **Invariant.** A two-branch affine cycle map with a 6-facet polygon invariant, instead of TM4's one inequality.

### How the .v file is organized

It imports only `Individual62`, `Arith`, `Lia` and `String` (no Longitudinal).

| section | lemma(s) in the .v |
|---|---|
| §3.1 shift rules | `ENDL AL BL AR BR ENDR D1L FLIP D0R OVL OVR FL FR1 FR2 FR3 FR4 FE0 FE1 FE2 FE3 FE4`, each `es`; plus `D0R'` (D0R with `01` carried along, for OV) |
| §3.2 repeated rules | `ALs BLs ARs BRs D1Ls D0R's`, each by induction on the exponent, with `lpow_shift'` to reorder the powers |
| §3.2 CTR, OV | `Fixpoint ctr k n` (C_k(n)), `ctr_even`, `ctr_odd`, `ctr_ones`, `ctr_pow`, `ctr_ov`; `CTR`; `OV`; the round trips `RT` (no overflow) and `OVRT` (overflow) |
| §3.2 QC | `QC` |
| §1, §3.3 R1–R3 | `Pc`, `Qc` (P and Q), `R1`, `R1s` (R1 repeated), `R2`, `Pfin` (R1 repeated then R2), `R3` |
| §3.3 conversion | `Hit0`, `Hit1`, `Inductive Gad G T D` (a gadget word G with T hits adding D A blocks), `gad_even`, `gad_odd`; `ConvNo` (no overflow), `PostOV` (QC rounds after an overflow), `ConvOV` (the overflow round r); `QG0`/`QG1` (from Q to the gadget); `Conv0` = R4, `Conv1` = R5, `Conv1o` = R5o |
| §4 cycle and invariant | `CfgF`, `Inv`, `cycle_step` |
| §5 start | `init0`, `init` |
| conclusion | `nonhalt`: `multistep_nonhalt` + `progress_nonhalt_cond` |

How the .v states the argument:

- **The counter value** is `Fixpoint ctr k n` (k digits, MSB first, via `Nat.div2`/`Nat.odd`), and `CTR` is one induction on k with an even/odd split of n.

- **The conversion is one generic induction.** `ConvNo` and `ConvOV` are proved by induction on a `Gad` derivation, so they hold for any gadget word, and `gad_even` and `gad_odd` build the two derivations of §3.3. `ConvOV` would also give R4o, but the .v applies it only to the odd gadget (`Conv1o`).

- **The progress index is one Q-phase step, not a whole cycle.** `CfgF k i y z := Q(k+2, 2^(k+1)+1+3i, 1+2i, y, z)` is the Q phase after i front steps.

In §4's terms, N = 2^(k+1), Y = y+2i and Z = z-i, so `CfgF 5 0 16 0` = S(6,16,0), and no negative numbers occur. `Inv` is the hexagon of §4 in these coordinates, plus N ≥ 64. `cycle_step` does one macro step: y ≥ 2 is one R3 (it leaves Y and Z unchanged, and Inv with them);

y = 0 is R4 then `Pfin`; y = 1 is R5 then `Pfin`, or R5o. Composed over one cycle, these steps are the cycle lemma of §4. Every side condition, and the hexagon's invariance, is a single `lia` call.

- **`nonhalt`** is `multistep_nonhalt` with `init` (17,215 steps), then `progress_nonhalt_cond` with index (k,i,y,z), configuration `CfgF` and invariant `Inv`.

## 7. Numerical sanity checks

These checks are independent of the .v; the result rests on the .v alone. The shift rules, the polygon's vertex check and the initial segment are exact computations.

The other items check parametric claims (CTR for all k and n, QC for every G, R1–R5o, the cycle lemma) over ranges and random samples;

their proofs are §3–§4 and the .v.

- **Shift rules (exact).** Each of the 21 shift rules of §3.1, executed on its window: every step count matches, F1 is never read, and the transitions used are all except F1.

- **Repeated rules (ranges).** AL/BL/AR/BR for a = 0..24; CTR for all 1,013 (k,n) with k ≤ 10, in 16t(n)+18 steps; OV for k = 1..10, in 16k+46 steps.

- **Macro rules (ranges and samples).** The chains of §3 were applied to concrete tapes, checking every rule's pattern at the head, and compared with the formulas of §2 and, for most instances, with direct simulation for exactly the summed step count.

  - Exhaustive over small parameters (one third also simulated): R1 2,793, R2 210, R3 12,096, R4 1,740, R5 954, R5o 393 instances, and R4o 428.

  - Random large parameters (k up to 11, blocks up to 300 or 2^(k-1)): 60 per rule, all also simulated.

  - The step formulas for R1–R3 match on every instance.

- **Cycle map (samples, plus an exhaustive integer check).**

  - At k = 6..11, 12 random invariant points per level, run through the rules of §3, and for k ≤ 8 also by direct simulation.

These 72 cycles use R1 13,124, R2 57, R3 5,770, R4 34, R5 23 and R5o 15 times, and R4o never.

  - All 316,911 integer points of R_N for N = 64..2048 map into R_2N and satisfy the cycle-lemma hypotheses (a)–(d). Their conversions are R4 158,810, R5 118,780, R5o 39,321, and R4o 0.

- **Polygon (exact).** Exact rational arithmetic confirms invariance for all N ≥ 64. The minimum slack is 3/128, attained at both vertices of the edge u = 1/8 (odd branch, facet 4Y+2Z ≥ N, 1/N = 1/64), and max(2u+v) on R is 27/32, at (3/8,3/32).

- **Initial segment and orbit.**

  - Direct simulation: c0 reaches Q(5,17,1,2,2) at step 1,507 and S(6,16,0) at step 17,215 (exact).

  - From step 1,507 to step 2,318,632,923, the rules of §3 alone reproduce 36 configurations of the direct simulation (first and last configurations of P and Q phases), with exact step numbers (§5).

They use R1 2,459, R2 7, R3 4,548, R4 7, R5 1 and R5o 3 times, and R4o never.

AI assistance: the proofs and original write-ups were produced with the help of Claude (Anthropic), with independent review and submission preparation by GPT-6 Astra (OpenAI).
