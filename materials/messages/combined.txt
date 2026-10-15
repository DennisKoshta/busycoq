**Eight BB(6) nonhalting proofs across five PRs**

I've submitted proofs for eight machines on the 698-holdout list:

• **Two sync bouncer counters:** two affine branches preserve one hexagonal invariant, including overflows that interrupt conversion.
https://github.com/ccz181078/busycoq/pull/24

• **One recursive Bell-eats-counter machine:** weighted potentials bound nested residue cleanup. This is a different blank start from the two in PR #22.
https://github.com/ccz181078/busycoq/pull/25

• **One spread-digit counter:** a return transducer reduces overflow behavior to four paths covered by one interval invariant.
https://github.com/ccz181078/busycoq/pull/26

• **One nested bell counter:** size and modulo-3 invariants prove safety by induction on execution length, without assuming that nested levels return.
https://github.com/ccz181078/busycoq/pull/28

• **Three bouncers with a complex edge:** separately proved openings reach the double-cycle law `(n,x) → (n + 12x + 808, x + 32)`.
https://github.com/ccz181078/busycoq/pull/27

Every file proves blank-tape nonhalting for its exact machine string. All eight compile against current busycoq BB6, have closed Print Assumptions, and pass coqchk. The PRs are awaiting review.

All write-ups (ZIP): https://raw.githubusercontent.com/DennisKoshta/busycoq/bbd8dec7ca70afd80523654b85ed142c3742e163/materials/all-writeups.zip
All space-time images (ZIP): https://raw.githubusercontent.com/DennisKoshta/busycoq/bbd8dec7ca70afd80523654b85ed142c3742e163/materials/all-images.zip

The existing busycoq constructions are credited in each PR. Feedback is welcome!

AI assistance: original proofs and write-ups with Claude (Anthropic); independent audit and submission preparation with GPT-6 Astra (OpenAI).
