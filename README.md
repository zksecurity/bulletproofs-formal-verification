# Formal Verification of Generalized Bulletproofs

Code artifacts, definitions and proofs for GBP/Bulletproofs built upon VCVio.

## Definitions

This repository contains definitions of:

- (k1,...,kn) (Computional) Special Soundness
- Honest Verififer Zero-Knowledge
- Completeness

For "sigma-style" protocols, using the formulations/ideas from "Compressed Sigma Protocols" where each protocol is viewed as 
an interactive reduction from its relation to the language of accepting last round messages:
the statement is the verifiers state and the proof is the last round message.

## Composition Theorems

Additionally, this repository contains compositions theorems stating e.g.

*Soundness:*
> If protocol A is (kA1,...,kAn)-special sound and protocol B is (kB1,...,kBn)-special sound,
> 
> then B ○ A (A followed by B) is (kA1,...,kAn, kB1, ..., kBn)-special sound

*Zero-Knowledge:*
> If protocol A is HVZK, then B ○ A is HVZK.

## Proofs

Finally, this repository contains proofs of:

- Generalized Bulletproofs (Arithmetization):
  - (Computional) $(n, q+1, 2 · n' · c + 3)$-special soundness
  - Completeness
  - Perfect HVZK
- Improved Generalized Bulletproofs (Arithmetization):
  - (Computional) $(n, q+1, 2 · c+5, 2)$-special soundness (observe this protocol has an additional round).
  - Completeness
  - Perfect HVZK
- Bulletproof folding:
  - 8 (Computional) Special Soundness
  - Completeness
- Simplified Bulletproof folding:
  - 4 (Computional) Special Soundness
  - Completeness


## Final Notes

This is part of a bigger project, a teaser, more exciting news to come...
