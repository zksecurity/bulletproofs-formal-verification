# Formal Verification of Generalized Bulletproofs

Code artifacts, definitions and proofs for GBP/Bulletproofs built upon VCV-io.

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
> If protocol $\Pi_A$ is $(k_A^{(1)},...,k_A^{(n)})$-special sound and protocol $\Pi_B$ is $(k_B^{(1)},...,k_B^{(n)})$-special sound.
> 
> Then $\Pi_B \circ \Pi_A$ (A followed by B) is $(k_A^{(1)},...,k_A^{(n)}, k_B^{(1)}, ..., k_B^{(n)})$-special sound

*Zero-Knowledge:*
> If protocol $\Pi_A$ is HVZK.
>
> Then $\Pi_B \circ \Pi_A$ is HVZK for any $\Pi_B$

These enable "composing" a tower of reductions, which is how folding is expressed in this project.

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

This is part of a bigger project (hence the lack of git history), a teaser.

More exciting news to come...
