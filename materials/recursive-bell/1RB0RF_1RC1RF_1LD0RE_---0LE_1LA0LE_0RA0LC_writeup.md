# 1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC: never halts

This machine moves a marker along its tape while incrementing a counter. When the marker reaches the counter, it consumes one digit and leaves a residue. Cleaning up that residue can start a nested copy of the same process.

The proof bounds the cleanup cost and shows that it always finishes before the next potentially unsafe consumption. This gives an infinite sequence of safe epochs, and hence nonhalting from the blank tape.

- Machine: `1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC`, viewer https://bbchallenge.org/1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC. A BB(6) holdout in the "Bell eats counter" class. Written for the string itself: no mirror, no state renaming.

- Template: `verify/FractalBEC.v`, `tm10` (`1LB0LF_1LC1LF_1RD1LB_---0RE_1RA0RE_0LA0RC`).

Mirrored, tm10 differs from this machine only in C1 (1RB there, 0RE here).

Its marker bounce `RInc` is this machine's bounce (§3.3, §3.5); its counter and its eat are not. tm10 eats its whole counter at every overflow.

This machine eats one digit at a time and leaves a residue, and one bounce can run a whole sub-epoch (D6, §3.8). §8.1 lists what is kept.

- Status: fully formalized.

The accompanying `1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC.v` (1,726 lines) proves `Lemma nonhalt: ~halts tm c0.` in Coq 8.20.1 against the busycoq BB6 framework, importing only `Individual62` from busycoq.

`Print Assumptions nonhalt`: Closed under the global context.

- Where each part lives in the .v (full table in §8.2): the rules of §3 and their soundness are Sections 1–3; one epoch and the start (§6) are Section 4; §4 and the counting phase are Sections 5–7; Lemma D (§5) is Sections 7–11.

The .v follows D.0–D.3 (positions, the nested digestion, the merged blocks) but replaces the excess profile of D.4–D.7 by two weighted exponent masses.

Its threshold is therefore N ≥ 17,705, and its finite part is 691 epochs (§8.3).

## Summary

- The tape is `(110)^a 0 (011)^b C> X`: a marker `0` between two runs of blocks, followed by a counter word `X`. Each bounce moves the marker one block to the right, adds 1 to `X` and spends one `011` of the budget `b` (rule B).

- At `b = 1` the machine eats the lowest digit of `X`. If the low block is an a-block, the eat gives new budget (E1g). A b-block or a bare tail ends the epoch at a left record (E2g, E0, Et1–Et3). The next epoch restarts with budget `N = k + 1` and a residue `Y` that is not a clean counter.

- The first bounces of an epoch digest `Y`. The digestion is recursive: at a b-block, one bounce runs a whole sub-epoch on the rest of the word (D6), and the next level of digestion runs nested inside the block that the sub-epoch leaves.

- The only halting transition, D reading 0, is reachable only through an eat at a word outside the counter grammar G (§4).

Lemma D (§5) shows that the digestion always ends inside the budget.

Its cost is about `2^(k/2)` for a counter with k blocks, against `N ≳ 2^(k+3)`.

A potential over the counter's positions bounds the cost and the number of positions the digestion creates, an invariant over epochs bounds the residue's exponents, and the epochs below the threshold are covered by running the rules-only model.

## 0. How the machine behaves

The tape is `(110)^a 0 (011)^b C> X`.

The `0` between the two block runs is a marker.

Each **bounce** moves the marker one block to the right, adds 1 to the counter word `X`, and costs one `011` block of budget (rule B).

This is FractalBEC's marker bounce.

When the budget `b` reaches 1, the machine **eats** the lowest digit of the counter.

The eat either gives more budget (E1g) or sweeps the whole `(110)^a` run into a new left record `L(k, T)` (E2g).

At a left record the next **epoch** restarts with budget `N = k + 1` and residue `T = 000 Y`.

The residue `Y` is not a clean counter, and the first bounces of the new epoch **digest** it.

The digestion is recursive: when it meets a 1-digit, one single bounce runs a whole sub-epoch on the rest of the word (rule D6).

Halting needs an eat to happen before the digestion has finished.

Lemma D shows the digestion always fits in the budget.

Its cost is about `2^(k/2)` with `k ≈ log2 N - 3`, so roughly `sqrt(N)`, against a budget of `N`.

## 1. The machine and its only halting transition

```
      0     1
 A   1RB   0RF
 B   1RC   1RF
 C   1LD   0RE
 D   ---   0LE
 E   1LA   0LE
 F   0RA   0LC
```

The only undefined transition is **D reading 0**. Every rule below is an exact run that never executes D0. So the machine halts only if the run reaches a configuration that no rule covers. Section 4 shows that the only such configurations are eats at a word outside the grammar G, and Lemma D shows these never occur.

## 2. Notation, families, words

- Configurations use the wiki/busycoq notation. `l q> r` means the head is in state q and reads the first symbol of `r`. `l <q r` means it reads the last symbol of `l`.

- Chunks: `a = 001`, `b = 101`, `z = 000`.

- A **block** is `c = d01 a^e`: an **a-block** if the digit `d = 0`, a **b-block** if `d = 1`. The **exponent** is `e ≥ 0`.

- Words are finite 0/1 strings taken up to trailing zeros. Written words are normalized: they have no trailing 0, and `X 0^inf` follows them. For example `'10' ≡ '1'` and `'00' ≡ ''`.

- **Tails:** `t0 = ''`, `t1 = 1`, `t2 = 010001`, `t3 = 110001`.

- **Grammar G (counter words):** `G ::= t_s | c (z c)* [z t_s]` with `s ∈ {1,2,3}` after a `z`.

  - The digits are LSB first. A word `W = c_0 z … z c_{k-1} [z t_s]` has **k = k(W)** blocks.

  - Its **value** is `m(W) = (4+s)·2^k + Σ d_i 2^i`, which lies in `[4·2^k, 8·2^k)`.

  - The clean words `D(k,s,v)` are the case where every block except the last has e = 1 and the last block has e = 0.

- **One-level residues O:** `'11' a^x z W`, `'01' a^x z W`, `'00' W`, `'10' W`, with `x ≥ 0` and `W ∈ G` (when `W = ''` the `z W` vanishes). O also contains the 23 **end words** `E*` listed in 3.4.

- **Hub words H:** `H ::= G | O | c z H`, i.e. a run of blocks in front of a G or O word.

- Families (a, b, k ≥ 0 as stated):

  - **Hub:** `K(a, b, X) := 0^inf (110)^a 0 (011)^b C> X 0^inf` with `b ≥ 1`. The `0` after `(110)^a` is the **marker**. The cells `x0-3..x0-1` hold the last `011`, and `X` starts at cell `x0`.

  - **Left record:** `L(k, T) := 0^inf <A 101 (001)^k T 0^inf`. Here A reads a blank.

  - **Pre-record:** `L'(k, T) := 0^inf E> 0 01 (001)^k T 0^inf`. This is one step before `L(k,T)`, since E0 = 1LA.

## 3. Rules

### 3.1 Window rules (finite runs; each is one `es`)

In each rule, every executed transition reads a cell inside the shown window. So each rule holds in **every** context.

| # | statement | steps |
|---|---|---|
| W1 | `1 F> 1 → 1 1 F>` | 5 |
| W2 | `F> 001 → 011 F>` | 3 |
| W3 | `F> 000 → 011 C>` | 3 |
| W4 | `C> 101 → 111 F>` | 9 |
| W5 | `011 E> 0 → E> 0 010` | 5 |
| W6 | `0 E> 0 → 1 1 F>` (marker turn) | 3 |
| W7 | `F> 01 → 00 F>` | 2 |
| W8 | `011 <A 100 → E> 001 000` | 4 |
| W9 | `011 <A 101 → E> 001 001` | 4 |
| W10 | `011 E> 1 → <A 100 0` (D6 exit) | 4 |
| W11 | `C> 10 → 11 F>` | 4 |

### 3.2 Shift rules (induction on n, one IH use each)

| # | statement | steps | proof |
|---|---|---|---|
| S1 (SL) | `(011)^n E> 0 → E> 0 (010)^n` | 5n | ind n: [W5, IH] |
| S2 (SR) | `F> (001)^n → (011)^n F>` | 3n | ind n: [W2, IH] |
| S3 | `1 F> 1^n → 1^(n+1) F>` | 5n | ind n: [W1, IH] |

### 3.3 Region pass (any left context `l`)

| # | statement | domain | steps | proof |
|---|---|---|---|---|
| RP0 | `l 0 (011)^n <A 100 X → l 110 0 (011)^n C> X` | n ≥ 1, any l, X | 8n+4 | W8, S1(n−1), W6, W7, S2(n−1), W3 |
| RP1 | `l 0 (011)^n <A 101 000 X → l 110 0 (011)^(n+1) C> X` | n ≥ 1 | 8n+7 | W9, S1(n−1), W6, W7, S2(n), W3 |

The region pass reads nothing to the left of the marker. That is why a bounce works in any left context (used in D6).

### 3.4 Local pass LP

**Definition.** `LP(X)` is the run from `011 C> X 0^inf` until the head first enters the cell left of that `011`, which is cell `x0-4`. LP never reads cell `x0-4` or anything to its left. Every rule below ends in one of two exit forms:

- **d = 0:** `<A 100 X'`;

- **d = 1:** `<A 101 000 X'`.

We write `LP(X) = (X', d)`.

| # | statement | domain | steps | proof |
|---|---|---|---|---|
| LP0 | `011 C> 0 r → <A 100 1 r` | any r (incl. X = '') | 4 | C0, D1, E1, E0 |
| LP11 | `011 C> 110 r → <A 101 000 r` | any r | 8 | C1, E1, E0, A1, F1, C0, D1, E0 |
| LPC (carry) | `011 C> 101 a^e z R → <A 100 001 a^(e+d_R) z R'` with `(R', d_R) = LP(R)` | e ≥ 0, R with an LP rule (R = '' allowed) | s(R)+8e+20 | right (3e+12): W4, S2(e), W3; then LP(R), whose exit reads the last cell of `(011)^e` or of `111`; left (5e+8): for e ≥ 1, W8 or W9, S1(e−1), then 9 fixed steps through `111` and the old `011`; for e = 0, 8 fixed steps |
| LP5 (D5) | `011 C> 10 001 a^e z R → <A 100 01 001 a^(e+d) z inc R` | R ∈ G (R = '' allowed) | by execution | right: 4 + W1-type step + S2; LP(R) = GI; left as in LPC |
| LP6 (D6) | `011 C> 10 101 a^e z R → <A 100 a^(k+1) z Y`, where `Φ(1, e+1, R) = L'(k, 000 Y)` | R ∈ G (R = '' allowed) | (3e+14) + sub-epoch + 4 | section 3.8 |
| LPT | six constant words, by execution (steps in brackets): `1 → 010001` [18]; `10010001 → 01001000010010001` [70]; `10110001 → 0001000010001` [44]; `1000010001 → 01000010010001` [40]; `1001000010001 → 010010001000010001` [62]; `10010010001 → 010010010001000010001` [100] (all d = 0) | — | 18–100 | es |

**GI (inc on G) is a corollary.** Write `inc W` for the LP result on a G word. It is a binary +1, LSB first:

- An a-block toggles to a b-block (LP0).

- A b-block carries (LPC): it becomes an a-block, and the rest is incremented.

- Tails step `'' → 1 → 010001 → 110001` (LP0, LPT, LP0).

- `110001 → 001` with d = 1 (LP11). This is an **overflow**: a new block, and the absorbed `001` goes into the block in front of it (LPC with `d_R = 1`), or into the hub when the word is a bare tail.

G is closed under inc. For a word with at least one block, inc returns d = 0. Positions are stable: inc changes digits, and on an overflow it adds +1 to the last block and appends a new last block with e = 0. It never changes any other exponent.

**Other names used below:**

- HT (toggle), D2 (`'01' V → '11' V`), D4 (`'00' V → '10' V`) and the tail steps are LP0.

- D1 (`'11' a V → '01' V`, d = 1), D3 (`'11' z V → '00' V`, d = 1) and `'11' → ''` are LP11.

- HC (carry into a nested word) is LPC with any rest that has an LP rule.

- D5 is LP5, D6 is LP6, and T is LPT.

**End words** E* is the closure of the LPT outputs and of `010010001` under LP until G (23 words, computed by direct enumeration). Its largest own-level cost until G is **τ = 13** bounces.

### 3.5 Bounce

**B.** `K(a, b+1, X) → K(a+1, b+d, X')` for `b ≥ 1`, `a ≥ 0` and `LP(X) = (X', d)`. Steps: `s_LP(X) + 8b + 4` (d = 0) or `+ 8b + 7` (d = 1).

- Proof: LP(X), then RP0 or RP1 with `n = b`.

- The run never reads left of the marker, so B also holds with any `l` in place of `0^inf (110)^a`.

### 3.6 Eats (b = 1; the LP exit then meets the marker, A reads 0)

| # | statement | context fact |
|---|---|---|
| E1g | `K(a, 1, a^(e+1) z R) → K(a+2, e+1, R)`, R ∈ G | never reads left of the marker |
| E2g | `K(a, 1, 101 a^e z R) →* L'(a, 000 11 a^(e+d') z R')`, `(R', d') = inc R`, R ∈ G | the sweep `110 → 010` through `(110)^a` reaches cell `first−1` only at the last step |
| E0 | `K(a, 1, '') →* L'(a+1, 0001)` | same |
| Et1 | `K(a, 1, 1) →* L'(a, 000 01 a z 1)` | same |
| Et2 | `K(a, 1, 010001) →* L'(a, 000 10 00 010001)` | same |
| Et3 | `K(a, 1, 110001) → K(a+1, 1, 001)`, then E1g gives `K(a+3, 1, '')`, then E0 | never reads left of the marker |

These cover every G word at b = 1. A G word is `''`, a tail, an a-block first, or a b-block first. Here `first` is the first cell of `(110)^a`. `L'(k,T) → L(k,T)` takes one step (E0 = 1LA on a blank).

### 3.7 Restart

**R.** `L(k, 000 Y) → K(1, k+1, Y)` in `3k + 7` steps, for any Y. The run never moves left of the A cell.

### 3.8 D6, the nested bounce

**Epoch map.** For `N ≥ 1` and a word `R`, `Φ(a, N, R)` is the deterministic sequence:

- B while b ≥ 2;

- the eats of 3.6 at b = 1;

- it stops at the first pre-record `L'(k, T)`.

Φ is defined when every eat it meets is at a G word. Inside D6 this holds: `R ∈ G` and G is closed under inc and under E1g.

**Φ terminates** for every `R ∈ G` (D.0, Lemma P): only E1g moves the front, finitely many positions are ever created, and between two eats the budget falls by 1 per bounce except for at most one bare-tail absorption. So Φ reaches E2g, E0, Et1, Et2 or the Et3 chain after finitely many steps, and LP6 below is a total rule. The same argument shows that the counting phase of every epoch (after its digestion) ends.

**LP6 proof.** Write `x0` for the first cell of X.

1. **Right pass (`3e + 14` steps).** It goes W11 (`C> 10 → 11 F>`), then W1, then F0 and A1, then S2(e), then W3:

   - from `011 C> 10 101 a^e z R`

   - to `011 1 · 110 0 (011)^(e+1) C> R`.

   The part after `·` is the hub `K(1, e+1, R)` whose `0^inf` has been replaced by `… 011 1`.

Its `first` cell is `x0+1`, so `first−1 = x0` holds a 1.

2. **Sub-epoch.** By 3.5 and 3.6, every bounce and every E1g of `Φ(1, e+1, R)` reads only cells at or right of its marker. Its final eat (E2g, E0, Et1, Et2, or the Et3 chain) reaches cell `first−1` for the first time in state E, exactly when the standalone run reaches `L'(k, T)`. So, cell for cell, the run in context equals the standalone run up to that moment, except that cell `first−1` holds 1 instead of 0.

3. **Exit (W10, 4 steps).** `011 E> 1 01 (001)^k T → <A 100 0 01 (001)^k T = <A 100 a^(k+1) T`. Every pre-record has `T = 000 Y`, so `X' = a^(k+1) z Y` and d = 0.

The sub-residue Y is one of:

- `'11' a^x z W'` with `W' ∈ G` (from E2g);

- `'1'` (from E0 and from the Et3 chain);

- `'01' a z 1` (from Et1);

- `'10 00 010001'` (from Et2).

All of these are in O ∪ G.

## 4. Coverage

**Lemma H.** Every H word has exactly one LP rule, and LP maps H into H.

Case split on the normalized word w:

1. **w ∈ G.** GI applies (LP0, LPC or LPT).

2. **w = c z H' with H' ∉ G.**

   - a-block: LP0.

   - b-block: LPC with `R = H'`, which has an LP rule by induction on length.

3. **w ∈ O**, by its prefix:

   - `11`: LP11. The result is `01 a^(x−1) z W`, or `00 W`, or `''`.

   - `01`: LP0. The result is `11 …`.

   - `00 W` with W ≠ '': LP0. The result is `10 W`.

   - `10 W`: by W.

     - W = '' or `t1`: the word is `t1`, or b-block `101` with R = ''.

     - W = `t2` or `t3`: LPT.

     - W starts with an a-block: LP5. The result is `01 a^(e+1+d) z inc R` ∈ O.

     - W starts with a b-block: LP6. The result is `a^(k+1) z Y` ∈ H.

   - E* words: by the table.

Closure holds because every output listed above is in H. Since normalization identifies `10` with `1` and `00` with `''`, each word has exactly one rule.

**Eats.** By 3.6 every G word at b = 1 has an eat rule. The eat leaves either a hub with a G word or a pre-record `L'(k, 000 Y)` with `Y ∈ H`. An eat at a word outside G is not covered and may halt; such an eat is **unsafe**.

**Corollary (one epoch).** Start an epoch at `K(1, N, Y)` with `Y ∈ H`.

- Bounces follow B while b ≥ 2. The budget b never increases: each bounce changes it by `d − 1 ≤ 0`.

- Let β be the budget used until the first hub whose word is in G ("digestion").

- If `β ≤ N − 2`, every eat of the epoch is at a G word. After digestion every word stays in G (GI, E1g), and the first non-E1g eat gives `L'(k', 000 Y')` with `Y' ∈ H`.

- The counting phase terminates (D.0), so this first non-E1g eat exists.

- Then `L` and R give the next epoch `K(1, k'+1, Y')`.

- The next budget satisfies `N' = k'+1 = N + 1 + A + Σ_{E1g}(e_i + 2) ≥ N + 1`, where A is the top-level absorption count.

## 5. Lemma D (the digestion fits in the budget)

**Lemma D.** For every epoch `t ≥ 3` of the orbit from the blank tape, `β_t ≤ N_t − 2`.

Notation for epoch t:

- The residue `Y_t` is **ordinary**, `'11' a^x z W` with `W ∈ G` (from E2g), or **special**: `Y_t ∈ G` (`'1'` from E0 or the Et3 chain; `t2` at epoch 3) or `Y_t ∈ E*` (`'01' a z 1` from Et1, `'10 00 010001'` from Et2).

- `k = k(W)` (k = 0 for a special residue). The exponents of W are `e_q` at **position** `q = 0..k−1`.

- The **excess** of a block is `η_q = e_q − 1`, or `e_q` for the last block. Suffix sums are `S_t(q) = Σ_{q' ≥ q} η_{q'}`, with `S_t(q) = 0` for `q ≥ k`.

- `L_t` is the number of D6 steps in the digestion. Level 1 is the top level; the sub-epoch of the j-th D6 creates level j+1.

- `c_t` is the number of positions created during the digestion (D.0).

- `κ_t = max_{3 ≤ s ≤ t} k_s` is the running maximum of k.

### D.0 Positions, the front, and the overflow bound

Fix an ordinary residue and follow its digestion.

**Positions.** The blocks of W are positions `0..k−1`.

A new position is created only by an **overflow**, a tail step `110001 → 001`.

This can happen anywhere: inside GI, in the inc of LP5 or E2g, in a counting bounce of a sub-epoch, or as Et3.

The new block `a(0)` is appended at the end.

The absorbed `001` goes to the old last block if there is one.

If the word being incremented is a bare tail, it goes to the context instead: the block `c'` of LP5, the exponent of E2g's residue, or the budget or `a` of the sub-hub.

`c_t` counts all of these, Et3 included.

Positions keep their index.

**Actions on W.** The **front** f is the lowest unconsumed position. Every step of the digestion that touches W is one of two kinds:

- an **increment** of the G word R formed by the unconsumed positions: a sub-epoch bounce (GI), the inc of LP5 or E2g, or Et3;

- a **consumption** of the front block: LP5 (strip, a-block), LP6 (trigger, b-block), E1g (a-block) or E2g (b-block).

All other steps leave W alone: LP0/LP11 on a level's O-prefix, and HT/HC through the merged blocks, which carry one step down to the deepest level. Positions are consumed in increasing order, because each level works to the right of the one before it.

The **W-phase** ends when the word of the deepest level enters G or E*. At that moment every position has been consumed. The reason: an O word followed by at least one block never parses as a G word. For example, `'00' 101 …` starts with `001 010 …`, which is not a block followed by `z`.

**(P1) One extra unit per position.** A block's exponent changes before its consumption at most once: +1, when it is the last block at an overflow. In that case a later position exists, so at its own consumption the rest R is not a bare tail, and the consumption absorbs nothing. Hence every position satisfies

`e_cur + d ≤ e_orig + 1`,

where d is the absorption at its consumption (LP5's d, E2g's d') and `e_orig = 0` for created positions.

**(P2) Increments per front.** Let `D_f` be the number of increments while the front is f.

- `D_0 = 0`, since level 1 strips its prefix before it consumes position 0.

- For f ≥ 1, **`D_f ≤ e_orig(f−1) + 1`**:

  - after LP5 or E2g at f−1 there is exactly one increment;

  - after LP6 or E1g at f−1 the (sub-)hub has budget `e_cur(f−1)+1`, which gives `e_cur(f−1)` bounces;

  - add at most one more, from a bare-tail absorption (b stays) or from Et3. Not both: after a bare-tail overflow, R has a block for as long as the front stays at f;

  - if `e_cur(f−1) = e_orig(f−1) + 1`, then R is never bare (P1), and there is no extra increment.

**Lemma P (potential).** Let V be the value of R, n its number of blocks, and `Z = 2^f·V`.

- `V ∈ [4·2^n, 8·2^n)`, so `⌊log2 Z⌋ = f + n + 2 =` (number of positions so far) + 2.

- An increment adds `2^f` to Z, since inc is binary +1 on the value, overflow included.

- A consumption replaces `(f, V)` by `(f+1, (V − d_f)/2)`, so Z does not increase.

Hence at every moment `Z ≤ m(W) + Σ_{f' ≤ f} 2^{f'} D_{f'}`.

**Lemma C (overflow bound).** If `c ≥ 1`, then

`3·2^{k+c} ≤ 9·2^k + Σ_{q<k} 2^{q+1} η_q − 5`.

*Proof.* Let `P = k + c`. Take the overflow that creates the last position, P−1. Just after it, `Z ≥ 2^{P+2}`, and the front is at most P−1. By Lemma P and (P2), with `m(W) ≤ 8·2^k − 1`, `e_orig + 1 = η + 2` for non-last original blocks, `η + 1` for the last one, and 1 for created ones:

`2^{P+2} ≤ 8·2^k − 1 + Σ_{q=0}^{P−2} 2^{q+1}(e_orig(q)+1) = 8·2^k − 1 + Σ_{q<k} 2^{q+1}η_q + 2^k − 4 + 2^P`. ∎

By Abel summation, `Σ_{q<k} 2^{q+1}η_q = 2S(0) + Σ_{q=1}^{k−1} 2^q S(q)`. So Lemma C reads

`2^c < 3 + (2/3)·[2^{−k}S(0) + Σ_{q=1}^{k−1} 2^{q−k−1} S(q)]`.

Consequences:

- A clean word (η ≡ 0) has c ≤ 1.

- A deep trigger with a large exponent in front of a short all-ones suffix can push c to about `log2(excess)`. Adversarial residues of this kind reach c = 2 to 6 (section 9).

- On the orbit itself, c ∈ {0, 1} on every epoch checked (section 9). The proof does not use this.

**Termination.** Lemma P applies unchanged to a lone sub-epoch `Φ(1, e+1, R)`, or to the counting phase of an epoch. There only E1g moves the front, and `D_0 ≤ e + 1`. It gives `3·2^P ≤ 9·2^{k(R)} + Σ 2^{q+1}η_q + e − 4`. So finitely many positions are ever created, there are finitely many E1g, and each phase between two eats is at most budget + 1 bounces. This is the termination used in 3.8.

### D.1 Cost recursion (from the rules)

Let `J(w)` be the number of own-level bounces until `w ∈ G`. Then:

- `J('11' a^x z W) ≤ 2x + 2 + J('10' W)`. The terms are LP11 and LP0 alternately: D1/D2 pairs, then D3 and D4. Equality holds unless a tail coincidence (D.3) ends the word earlier.

- `J('10' a-block(e) z R) = 2 + J('11' a^(e+1+d) z inc R)` (LP5, then LP0).

- `J('10' b-block(e) z R) = 1 + 2·J(Y)` (LP6). After LP6 the word is `a^(k+1) z Y`. Its first block alternates LP0 and LPC, so Y is incremented once every 2 bounces and no absorption reaches the hub.

- End words: by the table, at most **τ = 13**.

At the top level the D1/D3 steps absorb (d = 1), so `β = J − A`. Unfold over the levels `j = 1..L+1`, where `x_j` is the residue exponent and `S_j` the set of a-block strips of level j:

`β ≤ (x_1 + 1) + Σ_{S_1}(e + d + 4) + Σ_{j ≥ 2} 2^j [(x_j + 1) + Σ_{S_j}(e + d + 3)] + (2^L − 1) + 2^L·τ`.

Check: this recursion equals the bounce-by-bounce β on every epoch checked (D.1 row in section 9).

### D.2 Levels consume positions

- Level 1 strips positions `0..p_1−1` and meets its trigger b-block at `p_1`.

- For `j ≥ 2`, the sub-epoch of level j consumes the trigger `p_{j−1}`, then its E1g a-blocks, then the E2g block `q_j ≥ p_{j−1}+1`. Its exponent gives `x_j = e_cur(q_j) + d'`.

- Level j then strips `q_j+1..p_j−1` and meets trigger `p_j ≥ q_j + 1`.

This gives `q_j ≥ 2j − 3` and `p_j ≥ 2j − 2`. The trigger `p_L` is an existing position, so `p_L ≤ k + c − 1`, and

**`L ≤ ⌊(k + c + 1)/2⌋`.**

A position q consumed at level j has `j ≤ (q+3)/2`. Positions include created ones, and created positions can be triggers. A position created while the front is at the bare tail cannot be a trigger: when a level meets it, it is still `a(0)`, unless its own sub-epoch has already eaten it.

Check: `L ≤ ⌊(k+c+1)/2⌋` and `2(L−1) + #strips ≤ k + c`.

### D.3 Shape after digestion, and the merged blocks

**Shape.** The digestion ends exactly when the deepest level's word enters G. By D.0 the front is then at the bare tail. This happens either through an end word (E*) or through a **tail coincidence**:

- `'11' a z 1 → '01' z 1 = 010001 = t2` (LP11);

- `'11' z 1 → '00' 1 = 001` (LP11);

- `'10' t0 = t1` and `'10' t1 = 101` (already in G after normalization), and `'11' z '' = 11 → ''` (LP11).

Enumerating every O word over a bare tail and every E* word gives these possible final words ρ of the deepest level:

```
'', 1, 010001, 110001, 001, 101, 001000010001
```

So ρ has at most one block, and that block has e = 0.

The post-digestion word is

`B_1 z B_2 z … z B_L z ρ`,

so **`k_post ∈ {L, L+1}`** and `m_post < 2^(L+4)`.

**Merged blocks, itemized.** `B_j` is the D6 block `a^(k'+1)` of level j, of exponent k'. It grows by the absorptions of level j+1 (via HC). Let `C_j` be the positions consumed by the sub-epoch of level j+1 and by level j+1's strips.

- **For j < L**, `C_j = {p_j, …, p_{j+1}−1}` and `e(B_j) = Σ_{q∈C_j}(e_cur(q) + 2) − 2`.

  - The sub-record is `k' = 1 + e_cur(p_j) + Σ_{E1g}(e_cur + 2)`: `a` starts at 1, gains 1 per bounce and 2 per E1g, and the budgets are `e+1`.

  - Level j+1 then absorbs `x_{j+1} + 1 = e_cur(q_{j+1}) + 1` on its prefix (LP11 steps), and `e_cur + 2` per strip.

  - None of these levels meets a bare tail, because the front is left of `p_{j+1}`. So there are no other absorptions.

- **For B_L**, `C_L = {p_L, …}` is every remaining position, created ones included, and

  `e(B_L) = Σ_{q∈C_L}(e_cur(q) + 2) − 2 + (bare-tail absorptions) + τ_end`, with **`τ_end ≤ T := 5`**.

  The value of `τ_end` depends on how the deepest level ends:

  | ending | τ_end |
  |---|---|
  | sub-epoch ends in E2g, then strips; the end chain from `'10' t2` | 5 |
  | same, end chain from `'10' t3` | 2 |
  | same, ending in G otherwise | 0 |
  | Et2: +1 for the missing E2g, plus 4 for the chain of `'10 00 010001'` | 5 |
  | Et1: +1 for the missing E2g, plus 1 for the chain of `'01' a z 1` | 2 |
  | E0: +1 from E0's `a+1`, +1 for the missing E2g | 2 |
  | Et3 chain: the created position is in `C_L`, Et3's +1 is its overflow absorption, then E0 | 2 |

  T is the largest of these values.

**Mass bound.** For `1 ≤ J ≤ L`:

`Σ_{j=J}^{L} e(B_j) ≤ S_t(p_J) + 3(k + c − p_J) − 2(L − J + 1) + T`.

Reason: the positions consumed by levels ≥ J+1 are exactly those ≥ `p_J`.

- Each original one brings `e_orig + 2 ≤ η + 3`.

- Each overflow brings 1 (its absorption, wherever it lands in these levels), and its created position brings 2.

- The overflows counted here map injectively to created positions ≥ `p_J`.

### D.4 Excess flow

- **(e)** Every non-last block of every W has `e ≥ 1`, i.e. `η ≥ 0`.

  - A merged block has `e ≥ k' ≥ 1`.

  - ρ's block and blocks created after the digestion have e = 0 while last and e = 1 once an overflow passes them.

- Counting does not change any η. On an overflow, the old last block gains 1 and stops being last.

- The eat removes `h ≥ 1` leading blocks of the counted word. So `W_{t+1}[q]` is `B_{q+h+1}`, ρ's block, or a block created after the digestion. The last two kinds have η = 0.

**(a)** If `S_{t+1}(q) > 0`, then

`S_{t+1}(q) ≤ S_t(2q+2) + 3(k_t + c_t) + T − 8 − 6q`.

*Proof.* Let `J = q + h + 1 ≥ q + 2`. A positive suffix needs a merged block at position ≥ q, so `J ≤ L`.

1. Among `B_J..B_L` at most one is last, i.e. has `η = e` rather than `e − 1`. So `S_{t+1}(q) ≤ Σ_{j=J}^{L} e(B_j) − (L − J)`.

2. By the mass bound this is `≤ S_t(p_J) + 3(k + c − p_J) − 3(L − J + 1) + 1 + T`.

3. Use `p_J ≥ 2J − 2 ≥ 2q + 2`, `L − J + 1 ≥ 1`, and S nonincreasing (by (e)). ∎

**(b)** `x_{t+1} ≤ S_t(0) + 3(k_t + c_t) + T − 1`.

- By (P1) applied after the digestion, `x_{t+1} = e_cur + d' ≤ e(W_post[h−1]) + 1`.

- For `h ≤ L`, use `e(B_h) ≤ Σ_{j ≥ h} e(B_j)` and the mass bound.

- Otherwise `x_{t+1} ≤ 1`.

**(r) Resets.** After a special residue, or an ordinary epoch with `L_t = 0`, the post-digestion word has at most one block with e = 0. So `S_{t+1} ≡ 0` and `x_{t+1} ≤ 1`. The special residues have c = 0 (no W) and `β ≤ τ`:

- `'1'` and `t2` are in G, so β = 0;

- `'01' a z 1 → '11' a z 1 → t2` costs 2;

- `'10 00 010001'` costs 11.

**(c) Unrolling.** Let `Δ_s := 3(k_s + c_s) + T − 8`, which is ≥ 0 when `k_s + c_s ≥ 1`.

Apply (a) along `q_0 = q`, `q_{i+1} = 2q_i + 2`, i.e.

`q_i + 2 = 2^i(q+2)`.

The chain stops at the first i with `q_i ≥ k_{t−i}` (there the suffix is 0), at a reset (r), or at epoch 3 (whose residue `t2` is special).

Since `k_{t−i} ≤ κ_t`:

**`S_t(q) ≤ n(κ_t, q)·max_{s<t} Δ_s`**, where `n(κ, q) := max(1, ⌈log2((κ+2)/(q+2))⌉)`.

### D.5 Value bound

- After digestion, `m_post < 2^(L+4)` (D.3).

- Counting adds at most one per bounce, and there are at most `N_{t+1} − 2` bounces.

- E1g halves the value.

- E2g leaves `m(W_{t+1}) = (m_eat + 1)/2`.

- Since `m(W) ≥ 4·2^k`:

**`2^(k_{t+1}+3) ≤ N_{t+1} + 2^(L_t + 4)`**, with `L_t ≤ ⌊(k_t + c_t + 1)/2⌋` (D.2), and `L_t = 0` after a special residue.

### D.6 Constants along the orbit

Lemma C bounds `c_t` by the profile `S_t`. D.4(c) bounds the profile by the earlier `k_s + c_s`. A fixed point turns the two into one induction. For `κ ≥ 0`, define:

- `U(κ, q) := n(κ, q)·Δ(κ)` and `xmax(κ) := U(κ, 0) + Δ(κ) + 7`, where `Δ(κ) := 3G(κ) + T − 8`;

- `Γ(k, κ) :=` the largest c with `3·2^(k+c) ≤ 9·2^k + A_k − 5`, where `A_k = 2U(κ,0) + Σ_{q=1}^{k−1} 2^q U(κ,q)` (and `A_0 = 0`). This is Lemma C with `S ≤ U(κ,·)` inserted.

- `G(κ) :=` the least `G ≥ κ` with `max_{k ≤ κ}(k + Γ(k, κ)) ≤ G` when Δ is computed from this G. It is reached by iterating from `G = κ`. The map is monotone in G and in κ, so G(κ) is nondecreasing in κ, and so are Δ, U and xmax.

| κ | 1 | 2 | 4 | 8 | 11 | 12 | 16 | 20 | 26 |
|---|---|---|---|---|---|---|---|---|---|
| G(κ) | 2 | 4 | 7 | 11 | 15 | 16 | 20 | 24 | 31 |
| Γ(κ, κ) | 1 | 2 | 3 | 3 | 4 | 4 | 4 | 4 | 5 |

**Orbit invariant.** For every epoch t ≥ 3 the following holds:

- **(I1)** `Y_t` is ordinary or special.

- **(I2)** If ordinary: `η ≥ 0`, `S_t(q) ≤ U(κ_t, q)` and `x_t ≤ xmax(κ_t)`.

- **(I3)** `c_t ≤ Γ(k_t, κ_t)`, hence `k_t + c_t ≤ G(κ_t)` (c = 0 if special).

- **(I4)** `N_t ≥ N_lo(κ_t) := 2^(κ_t+3) − 2^(⌊(G(κ_t)+1)/2⌋+4)`.

*Proof by induction on t.*

- **Epoch 3:** `κ = 0`, special.

- **(I2) at t+1:** from D.4(a)–(c) and (r).

If `L_t = 0` (in particular whenever `k_t + c_t = 0`, since a trigger needs a position), (r) gives `S_{t+1} ≡ 0` and `x_{t+1} ≤ 1 ≤ xmax`.

Otherwise `k_t + c_t ≥ 1`, so `Δ_t ≥ 0`.

Use `Δ_s ≤ 3G(κ_s) + T − 8 = Δ(κ_s) ≤ Δ(κ_{t+1})` by (I3) at the epochs s ≤ t.

Also `n(κ_t, q) ≤ n(κ_{t+1}, q)`, and `x_{t+1} ≤ S_t(0) + Δ_t + 7 ≤ xmax(κ_{t+1})`.

(`U(κ, q)` is only used for `q < k ≤ κ`, so `κ ≥ 1` and `Δ(κ) ≥ 0` there; `xmax(0) = 1`.)

- **(I3) at t+1:** Lemma C with (I2).

- **(I4) at t+1:** if `κ_{t+1} = κ_t`, use `N_{t+1} > N_t`. Otherwise `k_{t+1} = κ_{t+1}`, and D.5 with `L_t ≤ ⌊(G(κ_t)+1)/2⌋ ≤ ⌊(G(κ_{t+1})+1)/2⌋` gives it.

- The induction also needs epoch t to finish, i.e. `β_t ≤ N_t − 2`. That is D.7.

### D.7 Assembly and the threshold

By D.1 and D.2, a position q consumed at level j carries weight `2^j ≤ 2^⌊(q+3)/2⌋`. By (P1), its cost is at most `e_orig + 4`:

- `x_j + 1 ≤ e_orig + 2`;

- a level-j strip costs `e_cur + d + 3 ≤ e_orig + 4`;

- a level-1 strip costs `e_orig + 5 ≤ 2(e_orig + 4)`.

The D6 terms and the end word give `(2^L − 1) + 2^L τ ≤ 2^⌊(k+c+3)/2⌋(τ+1)`. So

**`β ≤ Bnd := x + 1 + Σ_{q < k + c} 2^⌊(q+3)/2⌋ (e_q + 4) + 2^⌊(k + c + 3)/2⌋ (τ + 1)`**, with `e_q := e_orig` (0 for created positions).

**Worst case.** Write `Σ_q w_q e_q = Σ_q (w_q − w_{q−1}) S(q) + const`.

The weights `w_q` are nondecreasing, so Bnd is largest at `S = U(κ, ·)`, `c = Γ(k, κ)` and `x = xmax(κ)`.

Call the maximum over `k ≤ κ` **`Bnd_worst(κ)`**.

Under (I2) and (I3), `Bnd_t ≤ Bnd_worst(κ_t)`.

**Threshold.** Let `F := {κ : Bnd_worst(κ) + 2 > N_lo(κ)}`.

- Exactly, for κ < 160: `F = {0, …, 11}`.

- With **T = 5** and **τ = 13**: **`N* := max_{κ ∈ F} Bnd_worst(κ) + 2 = 14,796`**, attained at κ = 11.

For an epoch with `N_t ≥ N*`:

- if `κ_t ∉ F`: `β_t ≤ Bnd_worst(κ_t) ≤ N_lo(κ_t) − 2 ≤ N_t − 2` by (I4);

- if `κ_t ∈ F`: `β_t ≤ Bnd_worst(κ_t) ≤ N* − 2 ≤ N_t − 2`.

**Tail κ ≥ 64 (closed form).**

1.

*G is small.* Let `ℓ = log2(κ+2)` and `γ = log2(5κℓ)`.

Then `G(κ) ≤ G' := κ + ⌊γ⌋`.

Indeed `A_k ≤ 2^k U(κ,0)` and `U(κ,0) ≤ ℓ·3G'`, so `2^c ≤ 3 + ℓG' ≤ 5κℓ` while `G' ≤ 2κ`.

The fixed-point iteration therefore stays ≤ G'.

2. *Bnd is small.* With `Σ_q e_q ≤ S(0) + κ`:

   - `Bnd_worst(κ) ≤ 2^((G+3)/2)·(2U + Δ + κ + 4G + 22)`;

   - `2U + Δ + κ + 4G + 22 ≤ 20κℓ`;

   - so `Bnd_worst(κ) + 2 ≤ 2^(κ/2)·128(κℓ)^1.5`.

3. *The subtracted term in N_lo is small.* `2^(⌊(G+1)/2⌋+4) ≤ 2^(κ/2)·51(κℓ)^0.5`.

4. *Conclusion.* Both together are `≤ 2^(κ+3)` as soon as `2^(κ/2) ≥ 23(κℓ)^1.5`. This holds at κ = 64 (`4.3·10^9` against `1.8·10^5`), and the ratio increases from there on.

Both inequalities, and that the closed form dominates the exact value, were also checked numerically for 64 ≤ κ < 160, and `G(κ) ≤ κ + γ` for 16 ≤ κ < 160. So `F = {0..11}` for every κ.

### D.8 Finite part

- **Epochs with `N_t < 14,796`** (epochs 3 to 593, i.e. 591 epochs; epoch 594 has N = 14,819): the rules-only orbit is computed explicitly. It is the composition of the rules above, with no TM inside. None of these epochs has an unsafe eat or a word without a rule, and every one has `β_t ≤ N_t − 2`.

- The same orbit equals the TM left records to `10^11` steps: 517 epochs, N up to 12,668.

- The explicit check runs on to N = 400,000 (11,074 epochs) with every D-link verified (section 9). A longer run of the rules-only model reached N = 3.49·10^6 with no unsafe eat.

- The .v uses its own threshold, N ≥ 17,705, and runs the rules-only model inside Coq for 691 epochs, from epoch 3 to epoch 694 (N = 17,713); see §8.3.

## 6. Initial segment

From `c0 = 0^inf A> 0^inf`, by direct simulation:

- `L(1, 0001)` at step 28;

- `L(2, 0001000010001)` at step 124;

- `L(7, 000010001)` at step 304. The second epoch, `K(1,3,1000010001)` at step 137, eats at the non-G words `11000010010001` (step 213, giving `K(4,1,00010010001)` at step 228) and `00010010001`, and does not halt.

From `L(7, 000010001)` (epoch 3) on, everything follows from the rules: R, then B/LP, then the eats, then L', then L.

## 7. Conclusion

By induction on t ≥ 3:

- the TM reaches `L(k_t, 000 Y_t)` with `Y_t ∈ H`;

- `N_t = k_t + 1` grows by at least 1 per epoch;

- Lemma D gives `β_t ≤ N_t − 2` (jointly with the orbit invariant of D.6, which is carried along the same induction), so every eat of epoch t is at a G word (section 4);

- the epoch ends at `L(k_{t+1}, 000 Y_{t+1})`.

Every epoch takes at least `3k + 7 ≥ 1` steps, so the sequence of left records is infinite and the machine never halts.

**Why D0 is never read:**

- The only D-on-0 situations in the transducer are an F-turn two cells right of a 0, and E finding the pattern `010`.

- Every rule above is an exact run that avoids both.

- The only uncovered situation is an eat at b = 1 on a non-G word (for example `'11' z t3` = `11000110001` or `'00' t3` = `00110001`, where a forced eat halts).

- Lemma D rules that out.

## 8. The formal proof

### 8.1 The template

`verify/FractalBEC.v` proves its machines from three section hypotheses:

- `LInc`: +1 on a binary counter `L n` with 2-cell digits.
- `RInc`: the marker bounce below.
- `Ov`: the overflow, which eats the whole counter.

```
l |> R (1+n) m r -->+ l <| R n (1+m) r
R n m r = w1^n w0 w1^m r
```

An induction on the epoch number and `progress_nonhalt_simple` then give `nonhalt`.

`tm10` is the certificate `cert1 C A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]`, so w1 = `110` and w0 = `00`.

- **Kept:** `RInc`, mirrored, as RP0/RP1 (§3.3), proved like the template's by `es`; `es` for every finite run; `multistep_nonhalt` from an exact initial segment (`init` is one `solve_init`).

- **Not kept:** `LInc`, `Ov` and the induction on the epoch number. Here the counter has 3-cell blocks with exponents, `z` separators and a 4-stage tail (GI). An eat removes one digit and leaves a residue (E1g, E2g), and one bounce can run a whole sub-epoch (D6). The .v closes with an invariant on epochs and `progress_nonhalt_cond`.

### 8.2 How the .v is organized

Every lemma is top level (no Section, Module, Hypothesis or Axiom). Besides busycoq's `Individual62`, the file imports only the stdlib `Lia`, `String`, `List` and `Arith`.

| this write-up | .v section: definitions and lemmas |
|---|---|
| §3.1–3.7 finite runs | 1: `LP0`, `LP0z`, `LP11`, `LPCr`, `LPCl0`, `LPCl1`, `LP5r`, `LP5l0`, `LP5l1`, `LP6r`, `W10`, `RP0`, `RP1`, `E1r`, `E2l0`, `E2l1`, `Et0`–`Et3`, `Rst`, `LPT1`–`LPT6`. Each is one `es`, with symbolic exponents and an arbitrary left context `l` (and right context `r` where it is not `0^inf`). |
| §2 words, §3.4 LP, §3.8 Φ | 2: `word` (`t0`–`t3`, `blk d e w` = `d01 a^e z w`, `p11 x w`, `p01 x w`, `p00 w`, `p10 w`), `enc : word -> side`, and the mutually inductive `LP w w' d` and `Phi a b w k y`. D6 is the constructor `LP_6`, whose premise is `Phi 1 (S e) w k y`. |
| soundness of §3 | 3: `sound` (every `LP`/`Phi` derivation is a TM run, in every left context) |
| §3.7 restart, §6 | 4: `K`, `epoch_tm` (one epoch `K N y -->+ K (S k) y'`), `init` (`c0 -->* K 8 t2`) |
| §4, the rules as a program | 5: `lpf`/`phif` (fuel-bounded, computable), `model_sound` |
| G, GI, termination in 3.8 | 6: `gw`, `ginc`, `gval`, `ginc_LP`, `ginc_val`, `Psi` |
| 3.6 and 3.8 on G, D.1–D.3 | 7: `GPhi`, `GPhi_sound`, `gcount`; multi-step LP `LPs`, `LPs_hub`, `LPs_nest`; end chains `DigE`; digestion `DigP`/`DigT`, `Dig_sound`; `epoch_ord`, `epoch_spec` |
| D.0 and Lemma C | 8: `ginc_exps`, the Q potential `QI` (`QI_inc`, `QI_cons`, `QI_Ps`), the weighted potential `Pot` (`Pot_ov`, `Pot_inc`), `GPhi_pot` |
| D.1–D.3, D.5 | 9: `Dig_cost`, `Dig_mass`, `Dig_len`, `DigT_exists`, `GPhi_rel`, `GPhi_val` |
| D.6–D.7 | 10: the weights `w`, `v2` and bound functions `Pf`, `Af`, `Bf`, `Xf`, `Costf`, `Nlo`, `Nstar`; `N1`, `N2` |
| D.6, D.8, §7 | 11: `Inv`, `next_inv`, `inv_step`, `orbit`, `orbit_sound`, `fin694`, `inv694`, `nonhalt_from`, `nonhalt` |

Three details of the encoding:

- Normalization (`'10' ≡ '1'`, `'00' ≡ ''`) is an equality of tapes. `enc` ends in `const 0`, and the constructors `LP_eq`/`Phi_eq` accept any `w1` with `enc w1 = enc w2`.

- The context fact of 3.8 is part of the statements. The specifications of `LP` and `Phi` hold for every left context `l`, and the eat lemmas stop when the head first reads the last cell of `l`, which is the pre-record. So the D6 case of `sound` is just `LP6r`, then the sub-epoch's specification in the context `l 0111`, then `W10`.

- Lemma H is not stated as such. `DigT_exists` and `gcount` build the `LP`/`Phi` derivation for every word that the invariant allows, and the computable model covers the words of the finite part.

### 8.3 Lemma D in the .v

The .v proves Lemma D with D.0–D.3's picture (fronts, positions, the nested levels, the merged blocks), but it does the bookkeeping with potentials instead of the excess profile of D.4–D.7.

Notation for this section. For a counter word W with exponents `e_q` at positions q:

- `Mw(W) := Σ_q w(q) e_q`, with `w(q) := 2^⌊(q+1)/2⌋`, and `M2(W) := Σ_q 2^(q+1) e_q`;

- `P(κ) := max(12, κ + 3)`, `Ws(P) := Σ_{q<P} w(q)`, `v2(q) := 2^⌊q/2⌋` and `V2s(P) := Σ_{q<P} v2(q)`.

**Digestion as a relation (Section 7).** `DigP x W n c W'` says that the residue `'11' a^x z W` reaches the counter word `W'` in n own-level bounces with c absorptions. `DigT` is the same from `'10' W`. The constructors are D.1's recursion:

- the prefix: 2x + 2 bounces, x + 1 absorptions;

- LP5 at an a-block;

- LP6 at a b-block. Its sub-epoch is `GPhi 1 (e+1)` on the rest of the word, and the next level runs inside the new block (`LPs_nest`: n inner bounces are 2n outer ones, and the inner absorptions go into the block's exponent);

- the end words, as seven explicit chains (`DigE`: at most 13 bounces and 5 absorptions, ending in at most one block, with e = 0).

`DigT_exists` shows that every residue over a counter word has a digestion. `epoch_ord` composes a digestion with n + 2 ≤ N and the counting phase into one epoch `Phi 1 N`. The counting phase ends by `gcount`, which uses a simpler potential than Lemma P: `Ψ = m + b + Σ e − (number of blocks)` does not grow at a bounce (an overflow adds one exponent unit and one block, or one budget unit at a bare tail), and it drops by at least 3 at every E1g.

**Positions: Lemma C in potential form (Section 8).** During a digestion, let f be the front, R the unconsumed counter word (n blocks, value m, exponents `e_i` at positions f + i), and p the number of bounces still pending at the current level. Then

`Q := 2^f · (m + 2 Σ_i 2^i (e_i + 1) + p) ≤ Q_0 + 3·2^(f+n)`

holds throughout (`QI`):

- an increment trades one pending bounce for +1 on m;

- an overflow adds exactly `3·2^(f+n)` to both sides;

- a consumption of the front block never increases Q, and the next phase gets at most `e + 1` pending bounces (`QI_cons`, (P2));

- Et3 keeps it too.

Since `m ≥ 4·2^n`, this gives `2^(f+n) ≤ Q_0` (`QI_low`). So if `Q_0 < 2^(P+1)`, no position ≥ P is ever created (`QI_Ps`). At the start of a digestion, `Q_0 < 7·2^k + M2(W)`.

**Weighted potentials (Sections 8–9).** For nondecreasing weights v and constants α, β, γ, let

`Pot := Σ_{i<n} v(f+i)·(α e_i + β) + γ·Σ_{f+n ≤ q < P} v(q)`.

The second sum prepays the positions that do not exist yet. If `γ ≥ α + β + 1`, an increment never raises Pot, and an overflow lowers it by at least `v(f+n)`, which pays for a bare-tail absorption (`Pot_ov`, `Pot_inc`). `GPhi_pot` carries Pot through a whole sub-epoch and charges its record k at any level weight `U ≤ v`. The instances:

- **Cost** (`Dig_cost`: v = w, (α, β, γ) = (2, 8, 11)).

A digestion at nesting level ℓ (the top level is ℓ = 0) whose front is at `f ≥ 2ℓ` (D.2) satisfies `2^ℓ·n ≤ Pot + 2^ℓ (2x + 2) + 13 w(P)`.

At the top level this means the digestion takes at most `n ≤ 2 Mw(W) + 2x + 2 + 11 Ws(P) + 13 w(P)` bounces.

The position weights are D.7's: `w(q)(2e_q + 8) = 2^⌊(q+3)/2⌋ (e_q + 4)`.

- **Merged blocks** (`Dig_mass`: (α, β, γ) = (1, 3, 5)).

Take level weights u and position weights v with `u(ℓ) ≤ v(q)` whenever `2ℓ ≤ q`.

Then the post-digestion blocks weighted by their level, plus the absorptions c weighted by the parent level, are at most `Pot + u(ℓ−1)(x + 1) + 6 v(P)`.

This is D.3's mass bound in weighted form.

It is used with `(u(ℓ), v(q)) = (2w(ℓ−1), w(q))`, `(2^ℓ, 2^⌊q/2⌋)` and `(1, 1)`.

- **Length** (`Dig_len`): the post-digestion word has `k_post` blocks with `2(ℓ + k_post) ≤ P + 3` (D.2, D.3).

**Counting phase** (`GPhi_rel`, `GPhi_val`, `GPhi_rk`).

Counting starts at the hub with `a = 1 + n` and budget `b = N + c − n`, on the post-digestion word (value `m_post`).

It ends at the next pre-record `L'(k', 000 Y')` with `Y' = '11' a^x' z W'`, or with a special residue.

Then:

- the exponents of W' are those of the post-digestion word shifted down by h + 1 ≥ 1 positions, each raised by at most 1 (the last one not at all);

- x' is at most the eaten block's exponent + 1;

- `2 m(W') + a ≤ m_post + k' + 2`;

- `a + b ≤ k' + 1`, so `N' = k' + 1 > N`.

**The invariant** (`Inv κ N Y`, Section 11). Here κ bounds the number of blocks, like κ_t in D.6, and it is updated to `κ' = max(κ, k(W'))`. `Inv κ N Y` says:

- `N ≥ 17,705` and `N ≥ N_lo'(κ) := 2^(κ+3) − 8·2^⌊(P(κ)+3)/2⌋`;

- Y is special (`'1'`, `'01' a z 1` or `'10 00 010001'`), or `Y = '11' a^x z W` with `W ∈ G`, `k(W) ≤ κ`, `Mw(W) ≤ A(κ)`, `M2(W) ≤ B(κ)` and `x ≤ X(κ)`, where, with P = P(κ),

  - `A(κ) = 5 Ws(P) + 6 w(P) + 2 Ws(κ)`,

  - `B(κ) = A(κ) + 5 V2s(P) + 6 v2(P) + 2^(κ+1)`,

  - `X(κ) = A(κ) + 5P + 7`.

**Why it is preserved** (`inv_step`, `next_inv`).

- **(N1)** `7·2^κ + B(κ) < 2^(P(κ)+1)` for every κ. With `Q_0 < 7·2^k + M2(W)`, no digestion creates a position ≥ P(κ), so `k + c ≤ max(12, κ + 3)`. This replaces Lemma C's Γ and the fixed point G(κ) of D.6.

- **(N2)** The cost is `n ≤ Cost(κ) := 2X(κ) + 2 + 2A(κ) + 11 Ws(P) + 13 w(P)`. Moreover `Cost(κ) + 2 ≤ 17,705` for κ ≤ 11 (with equality at κ = 11), and `Cost(κ) + 2 ≤ N_lo'(κ)` for κ ≥ 12. So `n + 2 ≤ N`: the digestion fits in the budget. This is Lemma D, since `β_t ≤ n ≤ N_t − 2`.

- **The masses contract.** B_j, the D6 block of level j, is created at a trigger `p_j ≥ 2j − 2` (D.2), so the positions that pay for it have `w ≥ 2^(j−1)`; `Dig_mass` charges it at weight `2w(j−2)`. After the eat it sits at position j − 2 or lower of W', with weight at most `w(j−2)`. With κ' as above:

  - `2 Mw(W') ≤ Mw(W) + 5 Ws(P) + 6 w(P) + 2 Ws(κ') ≤ 2 A(κ')`;

  - `M2(W') ≤ Mw(W) + 5 V2s(P) + 6 v2(P) + 2^(κ'+1) ≤ B(κ')` (the v2-weighted potential is at most `Mw`, since `v2 ≤ w`);

  - `x' ≤ Mw(W) + 5P + 7 ≤ X(κ')`.

- **The lower bound on N.** If `k(W') > κ`, the value bound and `Dig_len` give `2^(k(W')+3) ≤ N' + 8·2^⌊(P+3)/2⌋`, as in D.5.

- **Special residues** digest by an end chain (at most 13 bounces), and the word after it has at most one block, with e = 0.

**Thresholds** (Section 10).

N1 and N2 are checked by `vm_compute` for κ ≤ 11 (`forallb` over `seq 0 12`).

Above that they follow by two-step inductions on κ, with bases κ = 10, 11 for N1 and κ = 12, 13 for N2.

The inductions use linear recurrences that hold for κ ≥ 9, among them `Ws(P+2) = 2 Ws(P) + 3`, `w(P+2) = 2 w(P)`, `A(κ+2) = 2A(κ) + 21` and `Cost(κ+2) + 10(κ+3) = 2 Cost(κ) + 121`, and the closed form `N_lo'(κ) = 2^(κ+3) − 8·2^⌊(κ+6)/2⌋`.

| κ | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|
| P(κ) | 12 | 12 | 13 | 14 | 15 | 16 |
| A(κ) | 1,419 | 1,451 | 2,219 | 2,923 | 4,459 | 5,867 |
| Cost(κ) + 2 | 8,725 | 8,853 | 13,471 | 17,705 | 26,931 | 35,389 |
| N_lo'(κ) | 1,024 | 3,072 | 6,144 | 14,336 | 28,672 | 61,440 |

**Finite part** (`fin694`, `inv694`).

The computable model `lpf`/`phif` consists of fuel-bounded functions with `model_sound`: every `Some` result is an `LP`/`Phi` derivation.

By `vm_compute` it runs from `K(1, 8, t2)` (epoch 3) through 691 epochs to `K(1, 17,713, Y_694)` (epoch 694), and `orbit_sound` makes this a TM run.

- `Y_694 = '11' a^7 z W` with `W = a(17) z b(1) z b(1) z b(1) z b(1) z a(1) z a(1) z a(1) z b(1) z a(0)`, so k = 10 and m(W) = 4,382.

- `Inv(10, 17,713, Y_694)` holds: `Mw = 77 ≤ 2,219`, `M2 = 1,054 ≤ 5,601`, `x = 7 ≤ 2,291`, and `N_lo'(10) = 6,144`.

`nonhalt` is `init`, then this orbit, then `progress_nonhalt_cond` with the invariant `∃κ, Inv κ N Y`.

## 9. Numerical checks

All of these are by direct simulation of the transition table, or by the rules-only model (no TM inside). They are evidence only; the result rests on the .v alone.

- **W1–W10, S1–S3:** in random contexts, n ≤ 13.

- **RP0/RP1:** n ≤ 30 with random X and l, step formulas 8n+4 and 8n+7.

- **LP rules:**

  - LP0: all r with |r| ≤ 10.

  - LP11: all r with |r| ≤ 9.

  - LPC and LP5: e ≤ 8 against G rests and non-G O rests, plus 100 large G words (exponents to 40).

  - GI as their composition, against the G-level inc: 300.

  - LPT: the 6 constant words.

- **D6:** the right pass (e ≤ 11, step formula 3e+14), and one TM bounce against the rules-only epoch map (250).

- **B:** in random left contexts, with the step formula and "never reads left of the marker" (500).

- **Eats:** E1g and E2g with a ≤ 400 and e ≤ 80 (600 each); E0 and Et1–Et3 for a ≤ 59.

- **R:** k ≤ 60 with random Y (200).

- **H1:** every word of an enumerated H sample (10,505 words: G with up to 3 blocks and exponents ≤ 2, all O forms, E*, 1–2 extra front blocks) has exactly one rule, its image is in H, and 700 are checked against a TM bounce.

- **H2:** every enumerated G word has an eat rule.

- **I:** initial segment exact (steps 28, 124, 304).

- **O1/O2:** the rules-only orbit equals the TM's left records, in a fresh simulation to 2·10^7 steps and against a stored log to 10^11 steps (517 records). The Coq model's orbit from `K(1,8,t2)` gives the same sequence N = 8, 16, 18, 32, 34, 45, 48, 62, 68, 84, 94, 104, ….

- **D.0/D.3 end of digestion:** an O word whose W has a block is never in G (11,360 random words). From every O word over a bare tail and every E* word, LP reaches G by LP0/LP11/LPT steps only and ends in ρ ∈ {'', 1, t2, t3, 001, 101, 001000010001} (87 words). T = 5 and τ = 13 are computed from the end chains.

- **Lemma D on the orbit:** every epoch of the rules-only orbit to N ≥ 400,000 (11,074 epochs; special residues: 4 in G, 1 end word). Overflows are counted everywhere: GI inside LP5/E2g/LPC, GI and batched counting inside D6 sub-epochs, and Et3. Checked:

  - Lemma C, `c_t ≤ Γ(k_t, κ_t)`, `k_t + c_t ≤ G(κ_t)`;

  - D.1 (exact), D.2, D.3, D.4(a)/(b)/(c)/(e)/(r), the bound on x;

  - D.5, `N_t ≥ N_lo(κ_t)`;

  - `β ≤ Bnd ≤ Bnd_worst(κ_t)` and `β ≤ N − 2`.

  - Observed on the orbit: c_t ∈ {0, 1} (7,137 / 3,937 epochs), β/Bnd ≤ 0.38. This is not used.

- **Adversarial residues:** about 27,000 (1,504 in each of two main runs and 12,004 in each of two stress runs). Two thirds come from inside the invariant of D.6 for random κ ≤ 16 (extreme or random profiles, all-ones suffixes, x up to `xmax`). One third are unconstrained, with η ≥ 0 and exponents up to 40.

  - Checked: Lemma C, D.2, D.3, D.4(a)/(b)/(e), `β ≤ Bnd`, and `c ≤ Γ`, `Bnd ≤ Bnd_worst` for the in-invariant ones; 40 whole epochs per main run against the TM.

  - Named cases: `'11' z b(17) z b(1) z t3` (c = 2), `'11' z b(8) z t1` at N = 100 (x_{t+1} = 17), a k = 3 case at N = 2917, and a k = 16 case (c = 4).

  - Largest slack used: D.4(a) −5 against the bound −3 (T − 8); D.4(b) 2 against the bound 4 (T − 1); c up to 6.

- **Threshold:** exact table for κ < 160 (F = {0..11}, N* = 14,796), monotonicity of G and U, `G ≤ κ + γ` for κ ≥ 16, and the closed-form tail for 64 ≤ κ < 160. The constants of §8.3 were tabulated for κ < 200: N1 holds, and `Cost(κ) + 2 > N_lo'(κ)` exactly for κ ≤ 11.

AI assistance: the original proof, proof sketch and checks were produced with the help of Claude (Anthropic); independent audit and submission preparation with GPT-6 Astra (OpenAI).
