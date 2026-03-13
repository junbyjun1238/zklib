# zklib roadmap

## North Star

Formalize reusable zk mathematics in Lean, then use that core to verify production-relevant verifier logic and eventually showcase deeper curve-specific results.

## Milestones

### M0: repository skeleton

- establish namespace and directory boundaries
- keep `Core`, `Instantiations`, and `Showcase` cleanly separated
- make it easy for contributors to land small, local changes

### M1: algebraic core

- prime-field operation signatures and derived law lemmas
- extension-field skeletons and later towers
- polynomial representation and evaluation
- cyclic evaluation-domain, coset, and root-of-unity lemmas
- NTT statement layer

### M2: verifier semantics

- typed transcript interface with explicit serialization boundaries
- constraint-system semantics
- verifier-oriented statement definitions

### M3: Ethereum-facing instantiation

- EIP-4844 statement layer
- setup-indexed KZG verifier specification boundaries
- clear separation between generic polynomial facts and commitment-specific assumptions

### M4: zkVM-facing instantiation

- FRI-oriented statement layer
- verification-key and statement-validity boundaries
- Merkle/transcript integration points
- receipt-verifier style decomposition

### M5: showcase theorem

- BN254 field tower
- curve and twist setup
- Miller loop and final exponentiation lemmas
- bilinearity statement for optimal Ate pairing

## Contribution Shape

The repository should prefer issues that land in one module at a time:

- one definition
- one lemma family
- one interface
- one protocol boundary

That keeps the project approachable even when the endgame theorem is research-grade.
