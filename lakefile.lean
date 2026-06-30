import Lake
open Lake DSL

package sigma where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-
We build on the VCV-io verified-cryptography library (the `OracleComp`/`ProbComp`
probability monad and its Σ-protocol layer). Mathlib comes in transitively via
VCV-io, so we deliberately do not add a second `require mathlib`: that keeps the
Mathlib revision pinned to exactly what VCV-io uses and avoids version conflicts.
-/
require VCVio from git
  "https://github.com/Verified-zkEVM/VCV-io.git" @
  "b87119da538df85375ab4893a5535ec76dcbcd41"

@[default_target] lean_lib sigma where
  roots := #[`Sigma]
