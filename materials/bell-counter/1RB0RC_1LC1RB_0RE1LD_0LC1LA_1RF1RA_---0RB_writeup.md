# `1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB` never halts

This machine keeps a binary counter at the right end of its tape. Left of the counter is a long word of `10` pairs, the *bell*, with a *wall* `00` in it. The counter's bits sit three cells apart, and a set bit is a `0` cell.

The head shuttles between the wall and the counter. Each round trip moves the wall two pairs to the right and subtracts 1 from the counter. At value 0, an overflow resets the counter according to the width of its zone modulo 3 (rules O0–O2 in §3.2).

When the bell is used up, the wall *bites* the low end of the counter. Usually the head then sweeps back to the left end of the tape, and everything left of the counter becomes the new bell. A bite that meets k low set bits instead opens k nested copies of the same process on the rest of the counter, one inside the other.

The machine can halt in only one way: a bite on an all-set counter with exactly two pairs of bell left. Two quantities rule this out forever. One is a size bound (the bell is long enough for the counter), and the other is a residue mod 3 that every cycle negates.

## Machine and status

- **Machine:** `1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB`, viewer https://bbchallenge.org/1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB
  - A BB(6) holdout in the "Bell eats counter" class.
  - Its only undefined transition is F0. The proof is written for the string itself, with no mirror and no renaming.
- **Template:** `verify/BECv5.v`, `Module TM1` (`1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA0RB`), architecture only.
  - Shared: a bell eaten by a binary counter, one `es` lemma per low-level rule, and one counter-form lemma per macro rule.
  - Different counter: it counts down, its bits sit 3 cells apart on a lattice anchored at its right end, and its overflow rule depends on the zone width modulo 3.
  - Different left side: a bite can open nested levels, so the left side of the tape is a stack of frames, one per pending level.
  - Different top level: TM1 ends with `progress_nonhalt_cond` over an invariant. Here termination of the nested levels is not known, so non-halting is a bounded induction on the number of steps (`U_all`). Its arithmetic is carried by invariants of a phase that every round preserves.
- **Status:** formalized. The accompanying `1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB.v` (1,039 lines) proves `Lemma nonhalt: ~halts tm c0.` in Coq 8.20.1 against the busycoq BB6 framework. It imports `Individual62` and the Coq standard library.
  - `Print Assumptions nonhalt`: *Closed under the global context*.

### Where each part lives in the .v

Every lemma is top level. §9 describes the formal proof in more detail.

| part of this write-up | names in the .v |
|---|---|
| §1 rule table | closing comment, in the parameters of the .v |
| §2 zones enc(w, v) | `bitc`, `dg`, `zone`, `dg_even`, `dg_odd`, `dg_zero`, `dg_full`, `dg_low`, `dg_lowones`, `lowbit` |
| §2 the family R_L(p, q, Z) | `RT`, `FR` (one frame), `lev`, `okL` |
| §3.1 low-level rules | `BR`, `SW` (= S), `TT` (= T), `PS`; `RND2`, `RND1`, `RND0` (W, PS^(q-3) and ZA as one run); `PUSH`, `BITE1`, `BITE0`, `BITE0c`, `BITE0c3` |
| §3.2 counter forms of the rounds | `R1z`, `R1t` (R1), `R2r`, `O2r`, `O1r`, `O0r` |
| §3.2 the round for any left context | `FR_round`, `lev_round`; the abstract round `Rnd` with `Rnd_tape`, `Rnd_valid`, `Rnd_exists` |
| §3.3 counter forms of the bites | `PUSHr`, `B1z0`, `B1z1`, `B1o`, `B1t`, `B0r`, `B0cr`, `B0c3r` |
| §3.3 ending bites | `EB` with `EB_tape`, `EB_lev`, `EB_valid` |
| §3.4 the stack | `iter_FR0`, `PUSH_lev`, `inner1` |
| §3.4, §5.7 nested bites, Lemma Kp | `Budget`, `Budget_step`, `JK`, `compose`, `STK` |
| §4, §5.5–5.7 the arithmetic of Lemmas K, A1 and Z' | phase invariants `KI`, `ZI` with `KI_step`, `ZI_step`, `KI_start`, `ZI_start`; all of them in `PI`, `PI_step`, `PI_start`; the walk to the bite `phase` |
| §5.1 definitions | `cap`, `Kst` (K), `Jst` (J), `Mv` (M), `Qv` (Q), `Ist` (I), `Kx` (K') |
| §5.2 Lemma P | `Saf`, `Saf_step`, `Saf_start`, `lowones`, `bite_shape` |
| §5.3, §5.5, §5.7 the plain ends | `ending`, `ending_B2` |
| §5.4 Lemma M | `Rnd_sign`, `EB_sign`; for rule N: `SR`, `SR_step`, `Mv_shift`, `pow2_mod3`, `QvN` |
| §6 bounded safety | `safe`, `safe_mono`, `safe_ev`, `safe_prog`, `safe_prog0`, `safe_RT0` |
| §6 the statement U(N) | `Post` ((U1)–(U4), plus the bound (U5) of §9.5), `U` |
| §6 U(N) for every N | `U_all` |
| §5.8, §6 closure of I and non-halting | `Ist_Kx`, `cycles`, `nonhalt` |
| §7 initial segment | `init` (327 steps), `init_I` |

## 0. Summary

The tape has three parts, from left to right:

- the *left part*, the stretch of bell the wall has already passed;
- the *bell* `(10)^q`, right of the wall `00`;
- a *zone* that holds a binary counter.

The counter's bits sit 3 cells apart, on a lattice anchored at the zone's right end. A zero cell on the lattice is a set bit.

The run is a sequence of *cycles*. A cycle starts with the head at the wall and no left part. It is made of the following moves.

- **Round.** The head runs from the wall to the zone and back. The wall moves 2 pairs right and the counter is decremented. At value 0 it *overflows*: the zone changes and the counter resets according to the zone width modulo 3 (rules O0–O2).
- **Bite.** When the bell is used up (q ≤ 2 pairs left of the zone), the wall bites the low end of the zone. Most bites end the cycle: the head sweeps back to the left end, and the left part becomes the new bell.
- **Nesting.** A bite that meets k ≥ 1 low set bits opens k nested *levels*. Each one is an ordinary cycle run on the rest of the zone, shifted right. Then the outer cycle continues.
- **Halting.** The only halting configuration is a bite at q = 2 on an all-set zone. It needs an overflow at exactly q = 4.

A cycle start is written as a triple `s = (n, w, v)`: bell length n, zone width w, counter value v. The proof is an invariant on cycle starts:

```
I = { w >= 3,  d = n - 2^(cap(w)+1) >= 2,  M(s) != 0 (mod 3) }  minus the single state (6, 4, 0)
```

Here cap(w) is the number of bits of a zone of width w, plus one when w ≡ 1 mod 3; §2 defines it.

- d ≥ 2 says that the bell is long enough for the counter.
- M is a mod-3 quantity that every cycle negates (§5.4).
- Inside a cycle, every level other than the first phase of the outer cycle starts in a parity class J that cannot reach the halting overflow (§5.3).

| piece | argument |
|---|---|
| low-level rules (BR, S, T, W, PS, ZA, PUSH, B1, B0, B0c, H tail) | exact TM runs, valid in every context (§3.1) |
| macro rules (round in 3 cases, B2, nested bite, B1, B0, B0c, H) | composed from the low-level rules; counter form (§3.2, §3.3) |
| levels, the stack and the shift law `G = F + 1` | tape argument (§3.4) |
| coverage and the phase lemma P | §5.2 |
| sign law (Lemma M) | one line per rule (§5.4) |
| Lemmas J, K, A1, Z', Kp; closure of I | §5.3, §5.5–5.8 |
| non-halting without termination | one bounded statement U(N), by strong induction on the number of steps (§6) |
| initial segment, 327 steps | exact run (§7) |

## 1. Rule table (busycoq comment-block style)

This block is a compact reference. §2 defines every symbol in it, and §3 derives every rule.

```
1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB            (only F0 is undefined)

lattice(w) = { j = w-1-3i : i >= 1, j >= 2 };   bit b of v (b = 0, 1, ...) sits on the b-th smallest lattice cell
enc(w,v)   = 1^w with 0 on the lattice cells of the set bits of v;   L(w) = #lattice(w) = floor(w/3) - 1
cap(w)     = L(w) + [w = 1 mod 3]                    allset(u) = enc(u, 2^L(u) - 1)
R(p,q,Z)   = 0^inf (10)^p 1 C> 0 0 (10)^q Z 0^inf  (p >= 0);   R(-1,q,Z) = 0^inf C> 0 0 (10)^q Z 0^inf  (cycle start)
             (Z never starts with 10: the bell takes every leading 10 pair; Z has no trailing 0)
R_L(p,q,Z) = L 0 0 (10)^p 1 C> 0 0 (10)^q Z 0^inf     (p >= 0, any left context L;  R = R_(0^inf))
R_L(-1,q,Z) = L C> 0 0 (10)^q Z 0^inf                  (only a name for the tape a level pops to)
             no rule is applied to R_L(-1, ..) unless L = 0^inf;  if L = L' 0 0 1 it is the tape R_L'(0, q, Z)

low-level rules (each run reads only the cells shown)
BR   B> 1^k              --> 1^k B>                                    k
S    (01)^k <C           --> <C (01)^k                                 2k       C1 D0
T    (111)^j <C          --> <C (011)^j                                5j       C1 D1 A1 C1 D0
W    C> 00 101010        --> 0101 0011 B>                              10
PS   011 B> (10)^b       --> 0 (10)^b 11 B>                            12b
ZA   00 (10)^a 11 B> 1^f 0  --> C> 0 (01)^(a+1) (011)^j 1              f = 2 mod 3, j = (f+1)/3
                            --> C> 0 (01)^(a+2) 111 (011)^(j-2) 1      f = 1 mod 3, f >= 4, j = (f+2)/3
                            --> C> 0 (01)^a 011111 (011)^(j-1) 1       f = 0 mod 3, f >= 3, j = f/3
PUSH C> 00 1010 (110)^k 111  --> 0101 (001)^k C> 00 101                14+3k   (k >= 0)
B1   00 (10)^p 1 C> 00 10 11 --> C> 00 (10)^(p+3) 1                    2p+15
B0   00 (10)^p 1 C> 00 1^f 0 --> C> 00 (10)^(p+2) 1 (011)^j 1          f = 2 mod 3, j = (f-2)/3
B0c  00 (10)^p 1 C> 00 1^w 0 --> C> 00 (10)^(p+2) 11 allset(w-2)       w = 0 mod 3, w >= 6
     00 (10)^p 1 C> 00 111 00 --> C> 00 (10)^(p+1) 111111              2p+31
Ht   C> 00 101 000       --> 0101 001 F> 0  (F0 undefined)             9

macro rules (Z = enc(w,v), f = position of the first 0 of Z, or w if v = 0; p >= 0 and any left context L;
             the five rounds also hold at p = -1 with L = 0^inf, where they give R(1, ..), §3.2)
R1   R_L(p,q,Z) --> R_L(p+2, q-2, enc(w, v-1))              q >= 3, v >= 1, w = 0,2 mod 3
R2   R_L(p,q,Z) --> R_L(p+2, q-3, enc(w+2, 2v-2))           q >= 3, v >= 1, w = 1 mod 3
O2   R_L(p,q,Z) --> R_L(p+2, q-2, enc(w+1, 2^(L+1)-1))      q >= 3, v = 0,  w = 2 mod 3
O1   R_L(p,q,Z) --> R_L(p+2, q-2, enc(w+1, 2^L-1))          q >= 3, v = 0,  w = 1 mod 3, w >= 4
O0   R_L(p,q,Z) --> R_L(p+2, q-3, enc(w+3, 2^(L+1)-2))      q >= 3, v = 0,  w = 0 mod 3
     (all five = W, PS^(q-3), ZA; 10 + 12(q-3) + f + 1 + 5j + {2(q-2) | 5+2(q-1) | 11+2(q-3)} steps)
B2   R_L(p,2,Z) --> R_L(p+2, 1, Z[2:])  re-parsed           Z starts 111, w >= 6    (PUSH k=0)
                (w = 1, bit 0 set: R_L(p+2, 2, enc(w-4, (v-1)/2)); never occurs, Lemma P)
N    R_L(p,2,(110)^k Y) --> R_L(p+2, G^(k-1)(3, Y[3:]))     k >= 1, Y starts 111, |Y| >= 6
H    R_L(p,2,(110)^k 111) --> halts                         k >= 1  (PUSH k, then Ht: 23+3k steps)
                (also k = 0, Z = 111: PUSH 0, then Ht; never occurs, since a bite zone has width >= 5, P1)
B1   R_L(p,1,Z) --> R_L(-1, p+3, Z[1:])  re-parsed          p >= 0, Z starts 11
B0   R_L(p,0,Z) --> R_L(-1, p+3, enc(w-3, (v-2)/2))         w = 0 mod 3, v >= 1 even
                --> R_L(-1, p+2, enc(w-1, (v-1)/2))         w = 0 mod 3, v odd      (never occurs, Lemma P)
B0c  R_L(p,0,1^w) --> R_L(-1, p+2, enc(w, 2^L-2))           w = 0 mod 3, w >= 6;   1^3 --> R_L(-1,p+1,1^6)
     ending bites (B1, B0, B0c) need the 0 0 left of (10)^p 1 and read nothing left of it

levels:  t = (n,w,v);  F(t) = the cycle start R(-1, F t) reached from R(-1, n, enc(w,v));
         the run from R_L(p0, n, enc(w,v)), p0 >= 0, n >= 3, pops at R_L(-1, F(t) + (p0+1, 0, 0))  (L never read);
         G(t) = F(t) + (1,0,0) = where a level started at R_L(0, n, enc(w,v)) pops
stack:   N = PUSH k, then the innermost level R_L1(0,1,Y[2:]) --B1--> (3, Y[3:]); level i pops into
         level i+1 (R_L(-1, ..) of level i = R_L'(0, ..) of level i+1); level k pops into R(p+2, ..)

invariant:  d(t) = n - 2^(cap(w)+1);  M(t) = n + 2v - 2^(cap+2) (w = 0,2) | n + v - 2^(cap+2) (w = 1)  (mod 3)
   K = { w >= 3, d >= 2 };   I = { t in K : M(t) != 0 } minus (6,4,0)
   J = { w >= 3, n >= 3, n odd if w = 1,2 mod 3 }               (inner phase starts)
   H* = { w = 2: n = 2v+4 } u { w = 1: v = 0, n = 2^(L+1)+4 }    (the phase starts that halt)
   s in I  ->  the cycle from s never halts, and if it ends, F(s) is in I   (M(F s) = -M(s))
start:  c0 -->(327) R(-1, 6, 11111) = (6,5,0),  d = 4, M = 2:  in I
```

## 2. Notation and families

### 2.1 Tape notation

`l C> r` means that state C reads the first cell of r. `l <C r` means that state C reads the last cell of l.

Words are written left to right, as on the tape. `0^inf` is a blank half-tape, and `x^k` is k copies of the word x.

### 2.2 Zones

A *zone* of width w is a word of w cells. Number its cells 0, 1, …, w-1 from the left. Its *lattice* is the set of cells

```
j = w - 1 - 3i      with i >= 1 and j >= 2
```

The lattice holds the bits of a counter value v.

- Bit b of v (b = 0, 1, …, L-1) sits on the b-th smallest lattice cell. So bit 0 is the leftmost one, and the counter is written least significant bit first.
- The index i in `j = w-1-3i` counts from the right. It is not the bit index.
- A set bit is a `0` cell. Every other cell of the zone is `1`.

`enc(w, v)` is the zone of width w with value v. The following quantities go with it:

```
L(w)      = floor(w/3) - 1                  the number of lattice cells (bits), for w >= 3
cap(w)    = L(w) + [w = 1 (mod 3)]
allset(u) = enc(u, 2^L(u) - 1)              every bit set
```

The lowest lattice cell is 2, 3 or 4 for w ≡ 0, 1, 2 (mod 3). The extra bit of cap(w) for w ≡ 1 is the cell 0, which becomes lattice cell 2 after an R2 round (§3.2).

A zone `enc(w, v)` always starts with `11`, so the bell parse is unambiguous. It contains no `00`.

**First zero.** f is the position of the first 0 of the zone, that is, of the lowest set bit. When v = 0, f = w. Then

```
Z = 1^f 0 r
```

For v = 0 the `0` here is the first blank cell, and r is empty.

**Cutting and re-parsing.** `Z[i:]` is Z without its first i cells, and `v >> 1` is floor(v/2). A cut zone is *re-parsed*: if it starts with `10`, that pair joins the bell.

### 2.3 The family

The configurations of the run are members of one family:

```
R_L(p, q, Z)   =  L 0 0 (10)^p 1 C> 0 0 (10)^q Z 0^inf      (p >= 0, any left context L)
R(p, q, Z)     =  R_L(p, q, Z) with L = 0^inf
R(-1, q, Z)    =  0^inf C> 0 0 (10)^q Z 0^inf               (a cycle start)
R_L(-1, q, Z)  =  L C> 0 0 (10)^q Z 0^inf
```

From left to right, `R_L(p, q, Z)` is a left context L, the wall `00` that ends L, the *left part* `(10)^p 1`, the wall `00` read by C, the bell `(10)^q`, the zone Z, and then blanks.

- Z never starts with `10`, since the bell takes every leading `10` pair. Z has no trailing 0.
- A *cycle start* is `R(-1, n, enc(w, v))`: no left part, blank left side. It is written as the triple t = (n, w, v).
- `R_L(-1, q, Z)` is only a name for the tape a level pops to. Rules are applied at p = -1 only with the blank left side (§3.2).
- For L = L' 0 0 1, the tape `R_L(-1, q, Z)` is `R_L'(0, q, Z)`. That is how an inner pop is read (§3.4).

### 2.4 Names for the parts of a run

- A rule from q ≥ 3 is a *round*. A rule from q ≤ 2 is a *bite*.
- B1, B0 and B0c are *ending* bites: they end the level, and p becomes -1. B2 and N are not ending bites.
- A *level* is a run of the family up to its own first ending bite, its *pop*, if there is one. Levels and their nesting are made precise in §3.4.
- A *phase* is the run of a level from its *phase start* (a level start, or the configuration after an N bite) to its next bite.
- Every phase start has q ≥ 3, except the innermost level of a nested bite. That one starts at q = 1 and is a single B1 (§3.4).
- Inside a phase, the zone passes through *stages*: stage 0 is the starting zone, and each overflow starts a new stage (§4). The stage at which a phase bites is m; it is also the number of overflows before the bite.
- The letter f always means the position of the first 0 of a zone.

## 3. Rules

### 3.1 Low-level rules (exact TM runs)

The transitions are:

```
A0 = 1RB    A1 = 0RC
B0 = 1LC    B1 = 1RB
C0 = 0RE    C1 = 1LD
D0 = 0LC    D1 = 1LA
E0 = 1RF    E1 = 1RA
F0 undefined    F1 = 0RB
```

Every rule below is a finite run that reads only the cells it shows. So it holds for every context left and right of them.

| rule | statement | steps | transitions |
|---|---|---|---|
| BR | `B> 1^k → 1^k B>` | k | B1 |
| S | `(01)^k <C → <C (01)^k` | 2k | (C1 D0)^k |
| T | `(111)^j <C → <C (011)^j` | 5j | (C1 D1 A1 C1 D0)^j |
| W | `C> 00 101010 → 0101 0011 B>` | 10 | C0 E0 F1 B0 C0 E1 A1 C0 E1 A0 |
| PS | `011 B> (10)^b → 0 (10)^b 11 B>` | 12b | per pair: B1 B0 T C0 E0 F1 B1 B1 |
| PUSH | `C> 00 1010 (110)^k 111 → 0101 (001)^k C> 00 101` | 14+3k | C0 E0 F1 B0 C0 E1 A1 (C0 E1 A1)^(k+1) S^2 |
| B1 | `00 (10)^p 1 C> 00 10 11 → C> 00 (10)^(p+3) 1` | 2p+15 | C0 E0 F1 B0 C0 E1 A1 S^(p+4) |
| Ht | `C> 00 101 000`: F reads a 0 after 9 steps | 9 | C0 E0 F1 B0 C0 E1 A1 C0 E0 |

**Pair step PS.** One pair starts from

```
0 1 1 B> 1 0
```

B1 moves on, then B0 writes 1, and C reads the third 1 of `111`. T leaves `<C 0 1 1 1`, with C on the leading 0. Then C0 E0 F1 B1 B1 give `0 1 0 1 1 B>`. The rule for b pairs follows by induction on b.

**Zone arrival ZA.** It starts from

```
00 (10)^a 11 B> 1^f 0        (f >= 2)
```

BR runs over `1^f`, and B0 writes 1 on the 0. That leaves

```
00 (10)^a 1^(f+2) <C 1
```

Then T^j consumes the 1s in threes from the right. What is left depends on f + 2 mod 3:

| f mod 3 | after T^j | finish | result | steps |
|---|---|---|---|---|
| 2 (j = (f+1)/3) | `0 1 <C` | S^(a+1) back to the wall | `C> 0 (01)^(a+1) (011)^j 1` | f+1+5j+2(a+1) |
| 1, f ≥ 4 (j = (f+2)/3) | `0 <C` | C0 E0 F1 B1 B0, then S^(a+2) | `C> 0 (01)^(a+2) 111 (011)^(j-2) 1` | f+1+5j+5+2(a+2) |
| 0, f ≥ 3 (j = f/3) | `0 1 1 <C` | C1 D1 A0 B1 B1 B0 T, then S^a | `C> 0 (01)^a 011111 (011)^(j-1) 1` | f+1+5j+11+2a |

Here `0 (01)^m` reads as `00 (10)^(m-1) 1`. So in each result, C stands on the first 0 of a new wall.

**Bites at q = 0.** B0 and B0c are the same arrival, with the wall itself as the start. `C> 00 1^f 0` runs C0 E0 F1 BR^(f-1) B0, then T^j, then the sweep S over the left part.

| rule | transitions | steps |
|---|---|---|
| B0 (f ≡ 2) | C0 E0 F1 B^(f-1) B0 T^((f-2)/3) S^(p+3) | f+3+5j+2(p+3) |
| B0c (w ≡ 0, w ≥ 6) | C0 E0 F1 B^(w-1) B0 T^((w-3)/3) C1 D1 A0 B1 B1 B0 T S^(p+2) | w+5j+2p+18 |
| B0c on `111` | C0 E0 F1 B^2 B0 C1 D1 A0 B^3 B0 T C1 D1 A0 B^2 B0 T S^(p+1) | 2p+31 |

**Ending sweeps.** In B1, B0 and B0c, the last S runs through the left part `(10)^p 1`, which reads as `1 (01)^p` from the right. Then D reads the second 0 of the `00` left of it, and C stops on the first one.

So an ending bite needs those two cells to be 0, and it reads nothing further left.

### 3.2 The round (R1, R2, O0, O1, O2)

Take q ≥ 3 and `Z = 1^f 0 r`. The round is W, then PS^(q-3), then ZA with a = q - 3. Reading the ZA result as a family member gives three cases by f mod 3:

```
f = 2 (mod 3):          R_L(p, q, 1^f 0 r) --> R_L(p+2, q-2, (110)^((f-2)/3) 111 r)
f = 1 (mod 3), f >= 4:  R_L(p, q, 1^f 0 r) --> R_L(p+2, q-2, 1111 (011)^((f-4)/3) 1 r)
f = 0 (mod 3), f >= 3:  R_L(p, q, 1^f 0 r) --> R_L(p+2, q-3, 11111 (011)^((f-3)/3) 1 r)
```

**Left context.** The round reads nothing left of the wall. It turns the wall and the first pair into `0101` (rule W). So for every L:

```
L C> 0 0 (10)^q Z   -->   L 0101 C> 0 0 (10)^q' Z'
```

- For p ≥ 0, L is followed by `0 0 (10)^p 1`, and `(10)^p 1 0101 = (10)^(p+2) 1`. So the output is `R_L(p+2, q', Z')`: the round holds for p ≥ 0 and every L.
- For p = -1, `L 0101 = L' 0 0 (10)^1 1` only when L = L' 0. Then `R_L(-1, q, Z)` goes to `R_L'(1, q', Z')`, and in particular `R(-1, q, Z)` goes to `R(1, q', Z')`.
- When L ends in 1, the output is one cell short of `R_L(1, ..)`. So the round at p = -1 is used only with the blank left side.

That is all the proof needs. The only level started at p = -1 is the outer one. An inner pop `R_L(-1, ..)` is re-read at once as `R_L'(0, ..)` with L = L' 0 0 1 (§3.4).

**Counter form.** For a zone enc(w, v), the first 0 is at the lowest set bit, and that bit's cell is ≡ w-1 (mod 3). When v = 0, f = w. Rewriting the three outputs in terms of enc gives five rules:

| rule | condition | output zone | q' |
|---|---|---|---|
| R1 | v ≥ 1, w ≡ 0, 2 | `enc(w, v-1)` (the decrement: clear cell f, set f-3, f-6, … ≥ 2) | q-2 |
| R2 | v ≥ 1, w ≡ 1 | `11·enc(w, v-1) = enc(w+2, 2v-2)` | q-3 |
| O2 | v = 0, w ≡ 2 | `enc(w+1, 2^(L+1)-1)`, all set, L+1 bits | q-2 |
| O1 | v = 0, w ≡ 1, w ≥ 4 | `enc(w+1, 2^L-1)`, all set, L bits | q-2 |
| O0 | v = 0, w ≡ 0 | `11·allset(w+1) = enc(w+3, 2^(L+1)-2)` | q-3 |

Rounds with q' = q-2 are *2-rounds*. R2 and O0 are *3-rounds*. A round never outputs a zone starting with `10`, so no re-parse is needed after a round.

### 3.3 Bites

| rule | from | to (counter form) | proof |
|---|---|---|---|
| B2 | `R_L(p, 2, Z)`, Z starts 111, w ≥ 6 | `R_L(p+2, 1, Z[2:])` re-parsed. w ≡ 0: `enc(w-2, v/2)`; w ≡ 2: `enc(w-2, v)`; w ≡ 1: `enc(w-2, v/2)` if bit 0 is clear, else `R_L(p+2, 2, enc(w-4, (v-1)/2))` | PUSH, k = 0 |
| N | `R_L(p, 2, (110)^k Y)`, k ≥ 1, Y starts 111, Y ≠ 111 | `R_L(p+2, G^(k-1)(3, Y[3:]))` | §3.4 |
| H | `R_L(p, 2, (110)^k 111)`, k ≥ 1 (k = 0: Z = 111) | halts after 23+3k steps | PUSH k, then Ht |
| B1 | `R_L(p, 1, Z)`, p ≥ 0 | `R_L(-1, p+3, Z[1:])` re-parsed. w ≡ 0: `(p+3, enc(w-1, v>>1))` if bit 0 is clear, `(p+4, enc(w-3, v>>1))` if set; w ≡ 1, 2: `(p+3, enc(w-1, v))` | B1 |
| B0 | `R_L(p, 0, Z)`, w ≡ 0 | bit 0 clear, v ≥ 1: `(p+3, enc(w-3, (v-2)/2))`; bit 0 set: `(p+2, enc(w-1, (v-1)/2))` | B0 |
| B0c | `R_L(p, 0, 1^w)`, w ≡ 0 | w ≥ 6: `(p+2, enc(w, 2^L-2))`; w = 3: `(p+1, enc(6, 0))` | B0c |

**The zones met at q = 2.** A zone starting `110` has its bit 0 set, so w ≡ 0. Then

```
Z = (110)^k Y
```

where k is the number of low set bits and Y = Z[3k:]. Either Y starts with `111` (its first lattice bit is clear), or Y is exactly `111` (all bits of Z are set). An enc zone of width ≡ 0 that starts with `111` and is not `111` has width ≥ 6.

**Two cases that never occur.** The zone `111` itself (w = 3, k = 0) halts at q = 2: PUSH 0 leaves `R_L(p+2, 1, 1)`, and Ht follows. It never occurs, because a bite zone has width ≥ 5 (P1 in §5.2).

B2 at w = 4 or 5 would need w ≢ 0 at q = 2, which never occurs either (P3).

### 3.4 Levels, the stack, and the shift law

**Levels.** A level is a run of the family started at `R_L(0, n, Z)` (an inner level, any L) or at `R(-1, n, Z)` (the outer level, blank left side), with n ≥ 3. It applies macro rules until its first ending bite. That bite leaves it at `R_L(-1, n', Z')`, the *pop*.

**Shift law.** Rounds, B2 and N read nothing left of the wall, and they add 2 to p. They hold for p ≥ 0 with any L, and the rounds also hold at p = -1 with the blank left side (§3.2).

The ending bites need p ≥ 0. They output q' = p + const, plus a re-parse that does not depend on p. Which rule applies depends on (q, Z) only. So:

- **(SL1)** Let n ≥ 3, and let p0 ≥ 0 with any L, or p0 = -1 with L = 0^inf. The run from `R_L(p0, n, Z)` applies the same rule sequence as the cycle from `R(-1, n, Z)`. Every p is larger by p0 + 1, and so is the pop's n'. So the run pops at `R_L(-1, F(t) + (p0 + 1, 0, 0))`.
  - The first rule is a round (n ≥ 3), and after it p ≥ 1. So no rule is ever applied at p = -1 with a nonblank left side.
- **(SL2)** In particular, a level started at `R_L(0, n, Z)` pops at `R_L(-1, G(t))`, where `G(t) = F(t) + (1, 0, 0)`.
- **(SL3)** The rest of a run after a configuration `R_L(p, q, Z)` with p ≥ 0 and q ≥ 3 is the run from that configuration. So (SL1) applies to it with p0 = p.

The only TM fact used is that an ending bite reads the two cells left of `(10)^p 1` and nothing beyond. For L = 0^inf they are blank. For an inner level they are the `00` of its `001` block (below).

**The stack (rule N).** Take `R_L(p, 2, (110)^k Y)` with k ≥ 1, Y starting `111`, and Y ≠ 111.

- **Step 1.** PUSH k gives `L 00 (10)^(p+2) 1 (001)^k C> 00 10 Y[2:]`.
  - Write `L_i = L 00 (10)^(p+2) 1 (001)^(k-i)`. Then this tape is `R_{L_1}(0, 1, Y[2:])`: level 1, the innermost.
- **Step 2.** Level 1 is one B1 bite (Y[2:] starts with 11). It pops at `R_{L_1}(-1, 3, Y[3:])`.
  - Y[3:] starts with `11`, so no re-parse is needed.
- **Step 3.** Since `L_1 = L_2 0 0 1`, the configuration `R_{L_1}(-1, q, Z)` is the same tape as `R_{L_2}(0, q, Z)`. So each pop is the next level's start.
  - Level i ≥ 2 starts at `R_{L_i}(0, t_i)`, with `t_2 = (3, Y[3:])` and `t_(i+1) = G(t_i)` by (SL2).
- **Step 4.** Level k pops at `R_{L_k}(-1, t_(k+1))`, and `L_k = L 00 (10)^(p+2) 1`. So that tape is `R_L(p+2, t_(k+1))`.
  - The outer level continues from there, with `t_(k+1) = G^(k-1)(3, Y[3:])`. For k = 1 this is `R_L(p+2, 3, Y[3:])`.
- **Step 5.** A nested bite inside a level does the same with that level's own L. Formally the stack is an induction on the length of the computation, since every inner level is a strictly shorter run.

With Y = 111, the innermost level is `R(0, 1, 1)`, and Ht halts: that is rule H.

**Composite form of a cycle with a continuation.** Let the first N bite of the outer level from s happen at `R(p_c, 2, Z_c)`, with k low set bits and `L_c = L(|Z_c|)` bits. Here p_c is in the outer frame, where p = -1 at the cycle start. Then

```
F(s) = (p_c + 2) + t_(k+2),     t_2 = (3, Z_c[3k+3:]),  t_(i+1) = G(t_i),     so  d(F s) = p_c + 2 + d(t_(k+2))
```

By the stack, the outer level resumes at `R(p_c + 2, t_(k+1))`. By (SL3) the rest pops at `F(t_(k+1)) + (p_c + 3) = t_(k+2) + (p_c + 2)`. Later N bites of the outer level lie inside this last G-step.

The cap of `t_2` is `L_c - k - 1`, because its zone drops the k + 1 low bits.

**Composite form for an inner level.** The same argument works for a level started at `R_L(0, t)`, with the first N bite at `R_L(p_c, 2, Z_c)`. Here p_c is in the level's own frame (p = 0 at the level start), and

```
G(t) = (p_c + 2) + t_(k+2)
```

In the frame of the cycle from t (p = -1 at the start) that bite is at p_c - 1. Then the formula reads `F(t) = (p_c + 1) + t_(k+2)`.

## 4. Cycle arithmetic

### 4.1 Stages of a phase

Fix a phase start (n, w, v) with w ≡ 0 or 2 (mod 3). Write c = L(w) (= cap(w)) and e = [w ≡ 2].

**Stage 0** is the initial zone. R1 rounds decrement v, so the zone becomes all clear at

```
q = E_0 = n - 2v
```

If E_0 ≥ 3, it overflows: by O2 (e = 1) or by O0 (e = 0).

**Stage i ≥ 1** has a zone with w ≡ 0 and c + i bits. It starts at value 2^(c+i) - 1 (after O2) or 2^(c+i) - 2 (after O0). It reaches 0 at

```
E_i = E_0 + i - e - (2^(c+i+2) - 2^(c+2))        (i >= 1)
```

and it overflows again (by O0) iff E_i ≥ 3. That gives

```
E_(i+1) = E_i + 1 - 2^(c+i+2)
```

**The bite.** The phase bites at the first stage m with E_m ≤ 2, at some q_b ∈ {0, 1, 2}.

- So m is also the number of overflows before the bite. Write u for the zone value there; it has c + m bits.
- Stage m starts at `Q_m = E_(m-1) - 3` for m ≥ 2, and at `Q_1 = E_0 - 3 + e` for m = 1.
- Inside stage m only 2-rounds (R1) happen. So q_b ≤ Q_m, with q_b ≡ Q_m (mod 2).

### 4.2 Position at the bite

Count the decrements of q:

```
n - q_b = 2·(#2-rounds) + 3·(#3-rounds)
```

The only 3-rounds are the m - e O0 overflows (m ≥ 1). Each round adds 2 to p, so for the outer level (where p starts at -1)

```
p_b = n - 1 - q_b - (m - e)
```

### 4.3 Reductions for w ≡ 1

- **(EQ1)** If v ≥ 1 and n ≥ 4, then `F(n, w, v) = F(n-1, w+2, 2v-1)`.
  - The R2 round from `(n, w, v)` and the R1 round from `(n-1, w+2, 2v-1)` both end at `R(1, n-3, enc(w+2, 2v-2))`.
  - Here cap(w+2) = cap(w), d drops by 1, and M is unchanged.
- **(EQ2)** If v = 0, then `F(n, w, 0) = F(n-2, w+1, 2^L - 1) + (2, 0, 0)`, with L = L(w).
  - O1 leads to `R(1, n-2, allset(w+1))`; then apply (SL3).
  - Here cap(w+1) = cap(w) - 1.

## 5. The invariant

### 5.1 Definitions

```
d(t) = n - 2^(cap(w)+1)          M(t) = n + 2v - 2^(cap+2)  (w = 0,2 mod 3);   n + v - 2^(cap+2)  (w = 1)   (mod 3)
K  = { w >= 3, d >= 2 }          I = { t in K : M(t) != 0 } minus (6,4,0)
J  = { w >= 3, n >= 3, n odd when w = 1 or 2 mod 3 }
H* = { w = 2 mod 3, n = 2v + 4 }  u  { w = 1 mod 3, v = 0, n = 2^(L+1) + 4 }
T_c = (2^(c+1)+2, 3c+5, 2^c - 1)        (w = 2 mod 3, d = 2, all set)
```

A state t is *zone-dominated* if d(t) ≤ 1, and *K-like* if d(t) ≥ 2. H* will turn out to be the set of phase starts that halt (P4).

**H* inside K.** We have

```
H* ∩ K = {T_c : c >= 0} ∪ {(6,4,0)}
```

- For w ≡ 2: `n = 2v + 4 ≥ 2^(c+1) + 2` forces `v = 2^c - 1`.
- For w ≡ 1: `2^(L+1) + 4 ≥ 2^(L+2) + 2` forces L = 0, so w = 4 and n = 6.

Also `M(T_c) = 2^(c+1) + 2 + 2^(c+1) - 2 - 2^(c+2) = 0`. And `H* ∩ J = ∅`, because H* has n even and w ≢ 0.

### 5.2 Lemma P (phase lemma, and coverage)

Take a phase start with q = n ≥ 3 and zone enc(w, v), w ≥ 3, that lies in J or in K. Then (P1)–(P5) hold.

**(P1)** Every zone in the phase is an enc zone, and after the first round its width is ≥ 5.

- The rounds map enc zones to enc zones (§3.2).
- Widths: R1 keeps w (≥ 6 when v ≥ 1), R2 gives w+2, O2 and O1 give w+1, and O0 gives w+3. In particular 3 → 6, 4 → 5 and 5 → 6.

**(P2)** Residues and parity.

- w ≡ 1 occurs only at the phase start: R2 leads to ≡ 0, and O1 to ≡ 2.
- w ≡ 2 occurs only at the start, or right after O1 at the start. R1 keeps it, and O2 leads to ≡ 0.
- w ≡ 0 is kept by R1 and O0.
- All rounds before the first 3-round or O2 are 2-rounds. So q keeps the parity of n while w ≢ 0.

**(P3)** The bite has w ≡ 0 and w ≥ 6, except a B1 at q = 1.

- q = 2 needs w ≡ 0. In J, n is odd while w ≢ 0. In K, stage 0 always overflows (E_0 ≥ 4, §5.5), and the case w ≡ 1, v = 0 overflows twice (O1, then O2 at q = n - 2^c ≥ 4).
- q = 0 happens only right after a 3-round at q = 3, and R2 and O0 leave bit 0 clear. So q = 0 means B0 with bit 0 clear (f ≥ 5), or B0c. The B0 case "bit 0 set" never occurs.
- B0c on `111` never occurs, since a q = 0 zone has width ≥ 6.
- So every configuration has a rule: a round for q ≥ 3; B2, N or H for q = 2; B1 for q = 1 (zones start with 11 and have width ≥ 4); B0 or B0c for q = 0.

**(P4)** The phase reaches H iff its start is in H*.

- H needs an all-set zone at q = 2. R1 never makes one (v - 1 < 2^L - 1). R2 and O0 leave bit 0 clear. O1 makes a w ≡ 2 zone, and q = 2 never meets one (P3).
- So H comes only from O2 at q = 4. O2 acts on a w ≡ 2 stage at v = 0. That is either the start, which reaches 0 at q = n - 2v, or the stage after O1, which reaches 0 at q = n - 2 - 2(2^L - 1) = n - 2^(L+1).
- q = 4 gives exactly H*. Conversely, from H* the O2 at q = 4 happens, and H follows.

**(P5)** Ending bites, and pop parity.

- B1 gives n' = p + 3 + r, where the re-parse r = 1 only for w ≡ 0 with bit 0 set (then w' = w-3 ≡ 0).
- B2 then B1 gives n' = p + 5 and w' = w - 3 ≡ 0.
- B0 gives n' = p + 3 and w' = w - 3 ≡ 0. B0c gives n' = p + 2 and w' = w ≡ 0.
- So a pop with w' ≡ 1 or 2 has n' = p + 3 ≡ p + 1 (mod 2). Every pop has w' ≥ 3 and n' ≥ p + 2.

### 5.3 Lemma J (inner phases)

**Lemma J.** If t ∈ J, the level from t never halts and never reaches a configuration without a rule. If it pops, it pops into J. The same holds for every phase of the level.

*Proof.*

- t ∉ H*. So by (P4) its first phase does not reach H, and by (P3) it never reaches a configuration without a rule.
- An inner level has p even: it starts at 0 and adds 2 per round.
  - An ending bite then gives n' ≥ p + 2 ≥ 4 (at least one round happened), w' ≥ 3, and n' odd when w' ≡ 1, 2 (P5). So the pop is in J.
- An N bite inside the phase has k ≥ 1 and Y ≠ 111 (no H). So |Y| ≥ 6, and `t_2 = (3, Y[3:])` ∈ J.
  - Its inner levels are levels from J. By induction on the length of the run, each pops into J if it pops.
  - The level resumes at `R(p_c + 2, t_(k+1))`, a phase start with t_(k+1) ∈ J.
  - By (SL3) its pop is `t_(k+2)` shifted by p_c + 2, which is even. So the pop is in J.

No termination is claimed. A level that never pops is still a run without a halt. □

The induction "on the length of the run" here, and in §5.4 (rule N) and §5.7, is made exact in §6. There Lemmas J, K, Z', Kp and M (for one level) are one bounded statement U(N), proved by strong induction on the number of steps N.

### 5.4 Lemma M (sign law)

Extend M to every family member. With σ = +1 for w ≡ 1 and σ = -1 otherwise, set

```
Q(p, q, Z) = q - (p+1) + σ v - (-1)^cap(w)    (mod 3)
```

At p = -1, Q = M, because `2^(cap+2) ≡ (-1)^cap` and `2v ≡ -v`.

**Lemma M.** Rounds, B2 and N keep Q. The ending bites negate it. So `M(F s) ≡ -M(s)`.

All congruences are mod 3, with `2^x ≡ (-1)^x`, `2 ≡ -1` and `v/2 ≡ -v` for even v. Write L = L(w).

**Rounds.** Q' is computed at p+2.

| rule | Q before | Q' after | why equal |
|---|---|---|---|
| R1 (w ≡ 0, 2) | `q-p-1-v-(-1)^L` | `(q-2)-(p+3)-(v-1)-(-1)^L` | differs by -3 |
| R2 (w ≡ 1, cap L+1) | `q-p-1+v+(-1)^L` | `(q-3)-(p+3)-(2v-2)+(-1)^L` (w+2 ≡ 0, cap L+1) | differs by -3-3v |
| O2 (w ≡ 2, v = 0) | `q-p-1-(-1)^L` | `(q-2)-(p+3)-(2^(L+1)-1)+(-1)^L ≡ q-p-4+2(-1)^L` | -4 ≡ -1, 2 ≡ -1 |
| O1 (w ≡ 1, v = 0) | `q-p-1+(-1)^L` | `(q-2)-(p+3)-(2^L-1)-(-1)^L ≡ q-p-4-2(-1)^L` | same |
| O0 (w ≡ 0, v = 0) | `q-p-1-(-1)^L` | `(q-3)-(p+3)-(2^(L+1)-2)+(-1)^L ≡ q-p-4+2(-1)^L` | same |

**Bites that keep Q.** This is B2, at q = 2. Q' is computed at p+2, with q' = 1.

| case | Q before | Q' after |
|---|---|---|
| B2, w ≡ 0 (v even) | `1-p-v-(-1)^L` | `1-(p+3)+v/2-(-1)^L ≡ -p-2-v-(-1)^L` (w-2 ≡ 1, cap L) |
| B2, w ≡ 2 | `1-p-v-(-1)^L` | `1-(p+3)-v-(-1)^L` (w-2 ≡ 0, cap L) |

**Ending bites.** Q' is computed at p = -1, and the claim is Q' ≡ -Q.

| case | Q before | Q' after |
|---|---|---|
| B1, w ≡ 0 (b0 = bit 0) | `-p-v-(-1)^L` | `(p+3+b0)-(v-b0)/2+(-1)^L ≡ p+v+(-1)^L` (cap L-1) |
| B1, w ≡ 2 | `-p-v-(-1)^L` | `(p+3)+v+(-1)^L` (w-1 ≡ 1, cap L+1) |
| B1, w ≡ 1 | `-p+v+(-1)^L` | `(p+3)-v-(-1)^L` (w-1 ≡ 0, cap L) |
| B0, w ≡ 0, bit 0 clear | `-p-1-v-(-1)^L` | `(p+3)-(v-2)/2+(-1)^L ≡ p+v+1+(-1)^L` (cap L-1) |
| B0, w ≡ 0, bit 0 set | `-p-1-v-(-1)^L` | `(p+2)-(v-1)/2+(-1)^L ≡ p+1+v+(-1)^L` (cap L-1) |
| B0c, w ≥ 6 | `-p-1-(-1)^L` | `(p+2)-(2^L-2)-(-1)^L ≡ p+1+(-1)^L` (cap L) |
| B0c on 111 | `-p-2` | `(p+1)+1 = p+2` (zone 1^6, cap 1) |

**Rule N, by induction on depth.** Let X_i be Q at the start of level i (p = 0). Each level keeps Q until its ending bite, which negates it. The pop (p = -1) has Q = -X_i, and the next level's start has Q one smaller (p+1 goes from 0 to 1). So

```
X_(i+1) = -X_i - 1,   i.e.   X_(i+1) - 1 = -(X_i - 1)     (mod 3)
```

Level 1 starts at `R(0, 1, Y[2:])`, where Y[2:] has w ≡ 1, value v_Y/2 and cap L - k. So

```
X_1 ≡ -v_Y - (-1)^(L-k)
```

The outer level resumes with `Q_out = -X_k - (p+3)`. At the bite configuration it had `Q_in = 1 - p - v - (-1)^L`, where `v = 2^k - 1 + 2^k v_Y`.

Substitute `X_k = 1 + (-1)^(k-1)(X_1 - 1)`. Then both sides equal

```
-p - 1 - (-1)^k (1 + v_Y) - (-1)^L
```

So `Q_out = Q_in`. □

### 5.5 Lemma K, plain cycles

**Lemma K.** Let s ∈ K, s ∉ {T_c, (6,4,0)}. The cycle from s does not halt, and if it ends, F(s) ∈ K. (T_c and (6,4,0) halt: they are in H*.)

*Halting.* The outer first phase halts iff s ∈ H* (P4), that is, iff s is T_c or (6,4,0). Every later phase starts in J (Lemma J). So the cycle does not halt.

*The bound, for w ≡ 0 or 2* (c = L(w), e = [w ≡ 2]).

- In K, `E_0 = n - 2v ≥ 2^(c+1) + d - 2(2^c - 1) = d + 2 ≥ 4`. So stage 0 overflows, and m ≥ 1.
- In a *plain* cycle (no N bite), the outer level ends at stage m with one of three endings. In each, cap(F s) = c + m - 1 (one bit is dropped), so `d' = n' - 2^(c+m)`.

| ending | n' | d' |
|---|---|---|
| E1: q_b = 1, B1 | p_b + 3 + b0 | n + 1 - m + e + b0 - 2^(c+m) |
| E2: q_b = 2, b0 = 0, B2 then B1 | p_b + 5 | n + 2 - m + e - 2^(c+m) |
| E0: q_b = 0, B0 | p_b + 3 | n + 2 - m + e - 2^(c+m) |

Here b0 is bit 0 of u. B0c cannot end an outer K cycle: it needs u = 0, so c + m = 1, but q_b = 0 needs m ≥ 2 (next item).

**Case m = 1.** E1 gives `d' = d + e + b0 ≥ d ≥ 2`. E2 gives `d' = d + 1 + e ≥ 3`.

E0 would need q_b = Q_1 = E_0 - 3 + e = 0, since q = 0 comes only right after a 3-round at q = 3 (P3). That is impossible, since E_0 ≥ 4.

**Case m ≥ 2.** Stage m is reached with Q_m = E_(m-1) - 3 ≥ q_b, so

```
n = E_0 + 2v >= q_b + 4 - m + e + 2^(c+m+1) - 2^(c+2) + 2v
```

Substituting into the table gives

```
d' >= X_m + 2e + 2v + [b0 in E1] + [2 in E2],     X_m = 2^(c+m) - 2^(c+2) - 2m + 6
```

`X_2 = 2`. For m ≥ 3, `X_m ≥ 4(2^(m-2) - 1) - 2m + 6 = 2^m - 2m + 2 ≥ 4`. So d' ≥ 2.

**Equality.** d' = 2 needs m = 2 and e = v = 0 (and b0 = 0 in E1), with Q_2 = q_b.

- The E1 case is `s = (2^(c+2)+3, 3c+3, 0)`, with F(s) = T_(c+1). This s has M(s) = 0, so it is not in I (its successor halts).
- The E0 case is `s = (2^(c+2)+2, 3c+3, 0)`, with `F(s) = (2^(c+2)+2, 3c+6, 2^(c+1)-2)`. That is in K and not in H*.

*The bound, for w ≡ 1 and v ≥ 1* (cap c = L+1). Use (EQ1) with

```
s~ = (n-1, w+2, 2v-1):   w+2 ≡ 0,  e = 0,  cap c,  v~ >= 1,  d~ = d - 1
```

- s and s~ have the same bite. Their first rounds (R2 and R1) are not overflows, and they lead to the same configuration. So m and q_b are the same for both.
- `E_0~ = n + 1 - 4v ≥ 2^(c+1) + 3 - 4(2^(c-1) - 1) = 7`.
- **E1, m = 1:** `d' = d - 1 + b0`, with Q_1 = n - 4v - 2 odd. So n is odd, d is odd, d ≥ 3, and d' ≥ 2.
- **E2, m = 1:** `d' = d~ + 1 = d`.
- **E0, m = 1:** it needs Q_1 = E_0~ - 3 = 0, which is impossible since E_0~ ≥ 7.
- **m ≥ 2:** `d' ≥ X_m + 2v~ ≥ 4`.

*The bound, for w ≡ 1 and v = 0.* Use (EQ2) with

```
s' = (n-2, w+1, 2^(c-1)-1):   w+1 ≡ 2,  all set,  cap c - 1,  d(s') = d + 2^c - 2 >= 2
```

s' = T_(c-1) only when n = 2^c + 4. With n ≥ 2^(c+1) + 2 that means c = 1 and s = (6,4,0). Otherwise `d(F s) = d(F s') + 2 ≥ 4`.

### 5.6 Lemma A1 (the bell at the first continuation)

**A1.** If the outer cycle from s ∈ K has an N bite, the first one is at `R(p_c, 2, Z_c)` with

```
p_c >= 2^(L_c) - 3
```

*Proof.* It happens at stage m, with q_b = 2 and b0 = 1. So p_c = p_b = n - 3 - m + e, and L_c = c + m.

- **m = 1:** `p_c - 2^(c+1) + 3 = d - 1 + e ≥ 1`.
- **m ≥ 2:** the bound on n of §5.5 (with q_b = 2) gives `p_c - 2^(c+m) + 3 ≥ X_m + 2e + 2v ≥ 2`.
- **w ≡ 1, v ≥ 1**, via s~. The configurations after the first round coincide, so p_c is the same, and `p_c = n - 4 - m`. For m = 1 this gives `p_c - 2^(c+1) + 3 = d - 2 ≥ 0`, tight at d = 2. For m ≥ 2 it gives ≥ X_m + 2v~ ≥ 4.
- **w ≡ 1, v = 0**, via s'. Here s' is in K, and it is not T_(c-1) unless s = (6,4,0); and (6,4,0) has no N bite, since it halts. So p_c = p_c(s') + 2, with the same L_c. □

### 5.7 Lemmas Z' and Kp (inner levels), and Lemma K for continuation cycles

**Kp.** If t ∈ J, d(t) ≥ 2 and the level from t pops, then d(G t) ≥ 3.

*Proof.* t ∈ K, and t is neither T_c nor (6,4,0): both have even n and w ≢ 0, so they are not in J. Lemma K gives d(F t) ≥ 2, and G = F + 1. □

**Z'.** If t ∈ J, d(t) ≤ 1 and the level from t pops, then d(G t) ≥ 2 or cap(G t) ≤ cap(t) + 1.

*Proof, for w ≡ 0 or 2.*

- With n ≤ 2^(c+1) + 1 we get `E_1 = E_0 + 1 - e - 2^(c+2) ≤ 2^(c+1) + 2 - 2^(c+2) ≤ 0`. So m ≤ 1.
- **m = 0, w ≡ 2:** n is odd, so q_b = 1, and B1 gives w' = w-1 ≡ 1 with all bits kept: cap' = c + 1.
- **m = 0, w ≡ 0:** there is no 3-round, so q_b ∈ {1, 2}. B1, or B2 then B1, drops bit 0: cap' = c - 1.
- **m = 1:** E1, E2 or E0 at stage 1 give cap' = c. B0c (u = 0, so c = 0) gives cap' = 1 = c + 1.
- **An N bite at stage m ≤ 1:** then L_c ≤ c + 1. With p_c in the level's own frame (p = 0 at the level start), the composite form is `G t = (p_c + 2) + t_(k+2)` (§3.4).
  - If some t_i (2 ≤ i ≤ k+2) has d ≥ 2, then by Kp so does t_(k+2), and d(G t) ≥ p_c + 4 ≥ 2.
  - Otherwise every t_i is zone-dominated. By Z' on each (shorter) inner level, `cap(t_(k+2)) ≤ cap(t_2) + k = L_c - 1 ≤ c`.

*Proof, for w ≡ 1* (n odd).

- **v ≥ 1, n ≥ 5:** (EQ1) gives `t~ = (n-1, w+2, 2v-1)` with w ≡ 0, cap c and d - 1 ≤ 0. Apply the w ≡ 0 case.
- **v ≥ 1, n = 3:** R2 goes to q = 0, then B0 (cap c - 1) or B0c (v = 1, cap c).
- **v = 0, n ≥ 5:** (EQ2) gives `t' = (n-2, w+1, 2^(c-1)-1)` ∈ J with cap c - 1. Z' or Kp for t' gives cap(G t) ≤ c, or d(G t) = d(G t') + 2 ≥ 4.
- **v = 0, n = 3:** O1 goes to q = 1, then B1 gives cap' = c. □

**Lemma K, continuation case.** Let s ∈ K \ {T_c, (6,4,0)} have an N bite, and let its cycle end. By the composite form,

```
d(F s) = p_c + 2 + d(t_(k+2)),      with t_2, ..., t_(k+2) in J (Lemma J)
```

- If some t_i has d ≥ 2, Kp carries it to t_(k+2), and `d(F s) ≥ p_c + 4 ≥ 4`.
- Otherwise every t_i is zone-dominated. Then `cap(t_2) = L_c - k - 1`, and Z' gives `cap(t_(k+2)) ≤ L_c - 1`. With n(t_(k+2)) ≥ 3 and A1:

```
d(F s) >= (2^(L_c) - 3) + 2 + 3 - 2^(L_c) = 2.
```

Also w(F s) = w(t_(k+2)) ≥ 3, so F(s) ∈ K. (On the continuation cycles we computed, the smallest value is d(F s) = 5, so this bound has slack.)

**Induction.** Lemmas K (for K), Z' and Kp (for J) are about runs that pop. Their proofs use the same lemmas for the inner levels of an N bite, and for the rest of the level after it. Each of these is a run that starts later, so it is shorter.

§6 states Lemmas J, K, Z', Kp and M (for one level) as one bounded statement U(N), and proves it by strong induction on the number of steps N. The proofs above are its induction step.

### 5.8 Closure of I

Let s ∈ I. Then:

- s ∉ H*: H* ∩ K = {T_c, (6,4,0)}, T_c has M = 0, and (6,4,0) is excluded from I.
- The cycle from s never halts (Lemma K).
- If it ends, F(s) ∈ K (Lemma K), and `M(F s) = -M(s) ≠ 0` (Lemma M).
- F(s) ≠ (6,4,0), because (6,4,0) has no predecessor in K. This follows from NB below and a finite computation.

**(NB)** Let m be the number of overflow rounds (O0, O1, O2) of the outer level before its first bite. Every cycle from s ∈ K that ends has

```
n(F s) >= n - m     and     2^(m-1) <= n
```

*w ≡ 0 or 2, first half.* By p_b (§4.2), a plain cycle has

```
n(F s) >= p_b + 3 = n + 2 - q_b - m + e
```

With q_b = 1 (E1, n' = p_b + 3 + b0) this is ≥ n + 1 - m. E2 and E0 give n + 2 - m + e. After an N bite, `n(F s) = p_c + 2 + n(t_(k+2)) ≥ p_b + 5 = n + 2 - m + e`, since n(t_(k+2)) ≥ 3 (Lemma J).

*w ≡ 0 or 2, second half.* We have m ≥ 1 (§5.5). If m ≥ 2, then stage m - 1 overflowed, so E_(m-1) ≥ 3 and

```
n >= E_0 >= 2^(c+m+1) - 2^(c+2) + 4 - m + e >= 2^(m+1) - m >= 2^m
```

*w ≡ 1, v ≥ 1.* By EQ1, F(s) = F(s~) with n(s~) = n - 1, and s and s~ have the same m (§5.5).

The bounds above hold for s~. They use no K-membership, only m ≥ 1 (E_0~ ≥ 7) and that B0c does not end the cycle (it would need c + m = 1, but c ≥ 1). So `n(F s) ≥ (n - 1) + 1 - m = n - m`, and `2^m ≤ n - 1` (or m = 1).

*w ≡ 1, v = 0.* By EQ2, F(s) = F(s') + (2, 0, 0) with n(s') = n - 2, and m(s) = m(s') + 1 because O1 counts. s' has w ≡ 2 and E_0' ≥ 4, so m(s') ≥ 1.

So `n(F s) ≥ (n - 2) + 1 - (m - 1) + 2 = n + 2 - m`, and `2^(m-1) ≤ n - 2` (or m - 1 = 1).

*Conclusion of NB.* n(F s) = 6 needs n ≤ 6 + m with 2^(m-1) ≤ n, which leaves n ≤ 10. The states of K with n ≤ 12 are finitely many: K forces cap ≤ 2 there. Running the cycle from each of them, none ends at (6,4,0).

So F(s) ∈ I. (The formal proof excludes (6,4,0) by a different bound, (U5) of §9.5, which needs no computation.)

## 6. Non-halting: induction on the number of steps

The argument is one strong induction on the number of TM steps. Lemma K's bound is used only for cycles that end within the steps considered. So termination of levels is never needed.

**Runs.** Let t = (n, w, v) with n ≥ 3. Let L be a left side and p0 ≥ 0, or p0 = -1 with L = 0^inf. Write run(L, p0, t) for the TM run from `R_L(p0, n, enc(w, v))`.

- Its *pop* is the first ending bite of its own level; ending bites of inner levels do not count. By (SL1) the pop is the tape `R_L(-1, F(t) + (p0 + 1, 0, 0))`.
- Write `K' = K \ ({T_c : c ≥ 0} ∪ {(6,4,0)})`.

**The statement U(N).** For every t ∈ J ∪ K' and every L, p0 as above: in its first N steps, run(L, p0, t) does not halt before its pop. If it pops within N steps, then

```
(U1)  t in J               ->  G(t) in J                                  (Lemma J)
(U2)  t in K'              ->  F(t) in K                                  (Lemma K)
(U3)  t in J, d(t) <= 1    ->  d(G t) >= 2  or  cap(G t) <= cap(t) + 1    (Lemma Z')
(U4)  M(F t) = -M(t)                                                       (Lemma M)
```

(U4) is Lemma M for one level: Q starts at M(t) - (p0 + 1) and ends at M(F t) + (p0 + 1), and the level negates it.

Kp is a case of (U2). A t ∈ J with d(t) ≥ 2 lies in K', because J contains no T_c and not (6,4,0). So d(G t) = d(F t) + 1 ≥ 3.

**U(N) holds for every N.** Assume U(N') for all N' < N, and take t, L and p0.

- **Step 1, the first phase.** By (SL1) it applies the rules of §3, with p shifted by p0 + 1. By (P1)–(P3) every configuration has a rule.
  - t is not in H*, since H* ∩ J = ∅ and H* ∩ K = {T_c} ∪ {(6,4,0)}. So by (P4) the phase does not reach H, and every other rule is a finite run that does not halt.
- **Step 2, a plain end.** If the first bite is an ending bite (B1, B0, B0c), or B2 followed by B1, that ending bite is the pop.
  - Then (U1)–(U4) are arithmetic on the first phase: (P5) as in Lemma J, the plain cases of §5.5, the plain cases of Z', and the per-rule tables of Lemma M.
- **Step 3, an N bite.** Otherwise the first bite is an N bite with k low set bits, at `R_L(p_c, 2, Z_c)`. PUSH takes 14 + 3k ≥ 17 steps. Then three runs come, one after the other:
  - the innermost level, one B1 bite, which leads to t_2 ∈ J;
  - level i = 2, …, k, which is run(L_i, 0, t_i);
  - the rest of the level, which is run(L, p_c + 2, t_(k+1)), from the tape where level k pops (SL3).
- **Step 3, continued.** Each of these runs starts after at least 17 steps, so U(N') with N' < N applies to it for the steps that are left.
  - If one of them does not pop within the steps left, the run has neither halted nor popped within N steps.
  - Otherwise each t_(i+1) is in J, and (U1)–(U4) hold for each t_i (i = 2, …, k+1). The pop of the rest is the pop of the run.
  - (U1)–(U4) then follow from the composite form (§3.4), A1, and the N-bite cases of Lemma J, Lemma K, Z' and Lemma M. The N row of §5.4 uses (U4) for the inner levels.
- **Step 4, w ≡ 1.** The cases of §5.5 and §5.7 for w ≡ 1 go through EQ1 and EQ2.
  - EQ1 changes only the first round. After it, the run is the same as the run from t~ after its first round, and steps 1–3 apply to it.
  - After the O1 of EQ2, the run is run(L, p0 + 2, t'), and U(N') applies to it for some N' < N.

**Non-halting.** Let s ∈ I. For every N, the run from R(-1, s) does not halt within N steps. By strong induction on N:

- By U(N), the cycle from s does not halt before it ends.
- If it ends within N steps, say after N_1 ≥ 1 steps, then F(s) ∈ I (§5.8, from (U2), (U4) and NB). The rest is the run from R(-1, F s) for N - N_1 < N steps. It does not halt, by the induction hypothesis.

By §7, the blank run reaches (6,5,0) ∈ I at step 327. So the machine never halts.

**Why F0 is never read.** F is entered only by E0. In every low-level rule except Ht, that E0 is followed by F1. Ht is the end of H, and H needs a phase start in H*.

## 7. Initial segment (exact)

From the blank tape, the first cycle starts are:

```
c0 = 0^inf A> 0^inf  -->(4)   R(-1,0,11)   -->(13) R(-1,1,11)   -->(26) R(-1,2,1)    -->(55) R(-1,3,111)
                     -->(116) R(-1,3,111111) -->(175) R(-1,4,111111) -->(244) R(-1,4,11110111)
                     -->(327) R(-1,6,11111) = (6,5,0)
```

The numbers are absolute step counts at the left records.

At (6,5,0) we have w = 5, cap = 0, d = 6 - 2 = 4 and M = 6 - 4 = 2. So it is in I.

The earlier states are outside K: they have w ≤ 2, or d < 2, or n ≤ 2. The .v runs these 327 steps directly (`init`).

## 8. Conclusion

### 8.1 Non-halting

By §7, the run reaches (6,5,0) ∈ I at step 327.

By §6 (strong induction on the number of steps), the run from a cycle start in I does not halt within N steps, for every N. Each cycle does not halt before it ends, and each cycle that ends starts the next one in I (§5.8). So the machine never halts.

### 8.2 Why it is not a cryptid

The rules are counter arithmetic: decrement, refill, and bites that drop 1 to 3 low cells. The nested bites are the same rules on a sub-zone.

The run has chaotic level-up transients: zones eaten down to 5–12 cells, and nesting depth up to 24 in the computed run. They never need exact tracking. They stay inside I, and the bound d ≥ 2 and the mod-3 class M ≠ 0 are all the proof uses.

### 8.3 What is not needed

Termination of levels and cycles is not proved, and it is not used: §6 is a strong induction on the number of steps. The formal proof follows that induction (§9.4).

## 9. The proof in Rocq

The .v proves the rules of §3 (all but the halting tail Ht), and it proves non-halting by the strong induction of §6. Its arithmetic is organised differently from §4–§5: as invariants of a phase that every round preserves.

### 9.1 Configurations

A zone is

```
zone r L v  =  1^r (1 1 c_0) (1 1 c_1) ... (1 1 c_(L-1)) 1 1 1,     c_b = 0 iff bit b of v is set
```

Its width is 3L + 3 + r, and `zone r L v = enc(3L+3+r, v)` with r = w mod 3 and L = L(w). The identities `dg_low` and `dg_lowones` split a zone at its lowest set bit and at its block of low set bits. They turn each round and bite into a list identity.

The family and the stack of levels are below. Lists left of the head are written outward from the head, so `FR p l` is the tape word `0 0 (10)^p 1` with l to its left.

```
RT l q Z  =  l {{C}}> [0;0] *> [1;0]^^q *> Z *> const 0
FR p l    =  [1] *> [0;1]^^p *> [0;0] *> l               (one frame)
lev P l   =  l  if P = 0  (then l must be const 0: okL),   FR (P-1) l  if P >= 1
```

So `RT (lev P l) q (zone r L v)` is `R_l(P-1, q, enc(w, v))`, with P = p + 1. The stack of levels is a stack of frames:

- a round turns `lev P l` into `lev (P+2) l` (`lev_round`);
- PUSH k puts k frames `FR 0` on top (`PUSH_lev`);
- an ending bite removes the top frame (`EB_tape`).

The shift law (SL1) is built in, because no rule lemma reads below the top frame.

### 9.2 Rules

Each low-level rule of §3.1 is one `es` call. The round is proved as a single run W, PS^(q-3), ZA, in three lemmas by f mod 3 (`RND2`, `RND1`, `RND0`). The halting tail Ht is not formalized, since the proof never runs it.

The counter forms of §3.2 and §3.3 are one lemma per rule (`R1z` … `O0r`, `PUSHr`, `B1z0` … `B0c3r`). The proof then works with two relations on parameters:

- `Rnd q r L v q' r' L' v'`: the six rounds of §3.2 (R1 for r = 0 and r = 2, R2, O2, O1, O0), with `Rnd_tape` (the tape step on any frame) and `Rnd_exists` (every q ≥ 3 has a round);
- `EB q r L v e r' L' v'`: the seven ending bites (B1 in four forms, B0, B0c, B0c on `111`). A bite from frame P pops with bell P + e.

The sign law of §5.4 is `Rnd_sign` and `EB_sign`, with `Qv P q r L v = M + 2P (mod 3)` for the Q of §5.4.

### 9.3 Phase invariants

The lemma `phase` walks a phase from its start to its bite (q ≤ 2), carrying any invariant that every `Rnd` step preserves. It needs no case analysis on overflows. The invariant `PI` of a level from t (in the .v's parameters, t = (n, r, L, v)) is the conjunction of:

- j even, where j is twice the number of rounds since the level start, and Q counted from the level start stays equal to M(t) (the sign law);
- r = 1 only at j = 0, and r = 2 with L = 0 only at j ≤ 2 (from (P2));
- `Saf`: Lemma P along the phase (no H, and every bite has a rule);
- `KI`, if t ∈ K': the bounds of Lemmas K and A1;
- `ZI` with C = cap(t) + 1, if t ∈ J and t is zone-dominated: the bound of Lemma Z'.

The three bounds read, in the .v's parameters (q the bell, zone r L v):

```
Saf q r L v
  r = 0:  (L = 0 -> q >= 3)  and  not (q = 2 and v = 2^L - 1)  and  (q = 0 -> v even)
  r = 1:  q >= 3  and  (v = 0 -> (q <= 2^(L+1) + 2 -> q odd)  and  q != 2^(L+1) + 4)
  r = 2:  (q <= 2v + 2 -> q odd)  and  q != 2v + 4

KI j q r L v
  r = 0:  2^L <= j + q  and  (2^(L+1) <= j + 2v + 2  or  2^(L+1) + 1 <= j + q)
          and  (q = 0 -> v != 0)  and  (L = 0 -> q >= 4)
  r = 1:  2^(L+2) + 2 <= q  and  (v = 0 -> 2^(L+1) + 5 <= q)
  r = 2:  2^(L+1) + 2 <= j + q  and  2v + 5 <= q

ZI C q r L v      (C >= 1)
  r = 0:  L <= C + 1  and  q + 2^(L+2) + C <= 2v + L + 2^(C+3) + 1  and  (q = 0 and v = 0 -> L <= C)
  r = 1:  L + 2 <= C  and  3 <= q <= 2^(L+2) + 1
  r = 2:  L + 1 <= C  and  q <= 2v + 2^(L+1) + 1
```

`Saf` is Lemma P in a form that every round keeps. For r = 0 it excludes H itself (q = 2 on an all-set zone) and the two bites without a rule (a width-3 zone at a bite, and B0 with bit 0 set). For r = 1 and r = 2 it excludes the states of H*, and it records the parity that keeps w ≢ 0 away from q = 2 (P2, P3).

`KI` replaces the overflow chain E_i of §4. At the bite it gives d(F t) ≥ 2 for every plain end, and `2^L ≤ j + 2` for a nested bite, which is A1.

In `ZI`, the quantity `q + 2^(L+2) - 2v - L` does not change under R1 and O0. So the bound allows at most one more overflow, as in the proof of Z'.

The starts with w ≡ 1 need no EQ1 or EQ2. Their bounds hold at the start (`Saf_start`, `KI_start`, `ZI_start`), and the first round maps them to the bounds for w ≡ 0 or 2.

### 9.4 The bounded statement

`safe c N` says that no halt happens within N steps from c. `Post t t'` collects what a level from t guarantees about the state t' = (n', w', v') it pops to:

```
(U1)  t in J               ->  G(t) in J
(U2)  t in K'              ->  t' in K
(U3)  t in J, d(t) <= 1    ->  d(G t) >= 2  or  cap(t') <= cap(t) + 1
(U4)  M(t') = -M(t)  (mod 3)
(U5)  w' = 4, v' = 0       ->  n' = 4  or  n' >= 8
```

Here t' is read in the cycle frame, as F(t) is, and G(t) = t' + (1, 0, 0). In the .v's parameters, w' = 4 is r' = 1 and L' = 0.

`U N` is §6's U(N) in continuation-passing form. Take a frame P, a left side l (blank when P = 0) and t ∈ J ∪ K'. If every pop t' with `Post t t'` is safe for N - 1 steps from `RT l (P + n') (zone r' L' v')`, then the level start `RT (lev P l) n (zone r L v)` is safe for N steps. No abstract cycle map F and no uniqueness of the pop are needed.

`U_all` proves U N for every N by strong induction. After `phase`, `bite_shape` splits the bite into three cases:

- an ending bite: the pop, with `Post` from `ending`;
- B2 then B1: `ending_B2`;
- a nested bite: `PUSH_lev` and `inner1`, then `STK` for the k - 1 pending levels, then U at fewer steps for the rest of the level at frame P + j + 2, then `compose`.

`STK` is the induction on the number of pending frames. It carries `Budget t C` (t ∈ K, or cap(t) ≤ C), which Kp and Z' pass from level to level (`Budget_step`), and the alternating sign relation `SR` of rule N. `compose` is the arithmetic of the composite form: the level pops at j + 2 plus the pop of the rest.

### 9.5 The bound (U5) in place of NB

(U5) says that a pop into width 4 with v = 0 has bell 4 or at least 8. So no cycle ends at (6,4,0), and NB of §5.8 is not needed.

- The only ending bite that outputs r' = 1 is B1 on a zone with r = 2 (width w ≡ 2 becomes w - 1).
- For L' = 0 that zone has width 5. By the second item of `PI`, a width-5 zone occurs only at j ≤ 2, and a bite comes after at least one round, so j = 2. That pop has n' = j + 2 = 4.
- After a nested bite the pop is n' = j + 2 + n3, with j ≥ 2 and n3 the pop of the rest of the level. By (U5) for the rest, n3 ≥ 4, so n' ≥ 8.

### 9.6 Cycles and the theorem

`Ist` is I (K' with M ≠ 0). `cycles` proves by strong induction on N that every cycle start in `Ist` is safe for N steps. It applies `U_all` with P = 0 and the blank left side, and takes the induction hypothesis as the continuation. The pop is in `Ist` by (U2), (U4) and (U5).

`nonhalt` combines `init` (the 327 steps of §7), `init_I` ((6,5,0) is in `Ist`) and `cycles`.

AI assistance: the original proof, proof sketch and checks were produced with the help of Claude (Anthropic); independent audit and submission preparation with GPT-6 Astra (OpenAI).
