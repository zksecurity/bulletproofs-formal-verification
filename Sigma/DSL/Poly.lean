/-
Copyright (c) 2026 Mathias Hall-Andersen. All rights reserved.
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
Authors: Mathias Hall-Andersen
-/
import Mathlib
import Sigma.DSL.Algebra

/-!
# Bounded polynomial operations for the protocol DSL

`BPoly A d` is a polynomial with coefficients stored up to degree `d`. This representation is
convenient for protocols like GBP, where the arithmetization fixes concrete degree bounds
for vector polynomials and commitment-coefficient families.

Division with remainder is exposed through Mathlib's unbounded `Polynomial` API. The DSL can
use bounded polynomials for typed protocol expressions and lower to `Polynomial` when it
needs Euclidean operations such as `(q, r) = p / vanishing`.
-/

namespace Sigma.DSL

universe u v w

/-- A polynomial with coefficients indexed by `0, ..., d`. -/
structure BPoly (A : Type u) (d : Nat) where
  /-- Coefficients of the bounded polynomial. -/
  coeff : Fin (d + 1) -> A

namespace BPoly

variable {A : Type u} {B : Type v} {C : Type w} {R : Type v} {d e : Nat}

instance [Inhabited A] : Inhabited (BPoly A d) where
  default := ⟨fun _ => default⟩

/-- Coefficientwise zero. -/
protected def zero [Zero A] : BPoly A d where
  coeff := fun _ => 0

instance [Zero A] : Zero (BPoly A d) where
  zero := BPoly.zero

/-- Coefficientwise addition. -/
protected def add [Add A] (p q : BPoly A d) : BPoly A d where
  coeff := fun i => p.coeff i + q.coeff i

instance [Add A] : Add (BPoly A d) where
  add := BPoly.add

/-- Coefficientwise subtraction. -/
protected def sub [Sub A] (p q : BPoly A d) : BPoly A d where
  coeff := fun i => p.coeff i - q.coeff i

instance [Sub A] : Sub (BPoly A d) where
  sub := BPoly.sub

/-- Coefficientwise negation. -/
protected def neg [Neg A] (p : BPoly A d) : BPoly A d where
  coeff := fun i => -p.coeff i

instance [Neg A] : Neg (BPoly A d) where
  neg := BPoly.neg

/-- Coefficientwise scalar multiplication. -/
protected def smul [SMul R A] (r : R) (p : BPoly A d) : BPoly A d where
  coeff := fun i => r • p.coeff i

instance [SMul R A] : SMul R (BPoly A d) where
  smul := BPoly.smul

/-- Constant polynomial. -/
def const [Zero A] (a : A) : BPoly A 0 where
  coeff := fun _ => a

/-- Evaluate a bounded polynomial. -/
def eval [Semiring A] (p : BPoly A d) (x : A) : A :=
  ∑ i : Fin (d + 1), p.coeff i * x ^ (i : Nat)

/-- The convolution coefficient used by bounded multiplication. -/
def mulCoeff [AddCommMonoid A] [Mul A] (p : BPoly A d) (q : BPoly A e)
    (k : Fin (d + e + 1)) : A :=
  ∑ i : Fin (d + 1), ∑ j : Fin (e + 1),
    if (i : Nat) + (j : Nat) = (k : Nat) then p.coeff i * q.coeff j else 0

/-- Bounded polynomial multiplication by coefficient convolution. The result degree is the
sum of the input degree bounds, so this is intentionally an explicit operation rather than
a `Mul (BPoly A d)` instance. -/
protected def mul [AddCommMonoid A] [Mul A] (p : BPoly A d) (q : BPoly A e) :
    BPoly A (d + e) where
  coeff := mulCoeff p q

/-- Coefficientwise map. -/
def map (f : A -> B) (p : BPoly A d) : BPoly B d where
  coeff := fun i => f (p.coeff i)

/-- Bilinear coefficient convolution. This covers expressions such as
`Poly.bilin (fun a b => ⟪a, b⟫) fL fR`. -/
def bilin [AddCommMonoid C] (op : A -> B -> C) (p : BPoly A d) (q : BPoly B e) :
    BPoly C (d + e) where
  coeff := fun k =>
    ∑ i : Fin (d + 1), ∑ j : Fin (e + 1),
      if (i : Nat) + (j : Nat) = (k : Nat) then op (p.coeff i) (q.coeff j) else 0

/-- Convert a bounded polynomial to Mathlib's `Polynomial` representation. -/
noncomputable def toPolynomial [Semiring A] (p : BPoly A d) : Polynomial A :=
  ∑ i : Fin (d + 1), Polynomial.C (p.coeff i) * Polynomial.X ^ (i : Nat)

/-- Project the first `d + 1` coefficients of an unbounded polynomial into a bounded
polynomial. This is a truncation unless the polynomial has degree at most `d`. -/
noncomputable def ofPolynomial [Semiring A] (d : Nat) (p : Polynomial A) : BPoly A d where
  coeff := fun i => p.coeff (i : Nat)

end BPoly

namespace Poly

variable {A : Type u}

/-- Vanishing polynomial of a finite set of points: `prod_x (X - x)`. -/
noncomputable def vanishing [CommRing A] (xs : Finset A) : Polynomial A :=
  xs.prod fun x => (Polynomial.X : Polynomial A) - Polynomial.C x

/-- Polynomial division with remainder over a field. This is the operation behind DSL code
like `(q, r) := p / vanishing`. -/
noncomputable def divRem [Field A] (p q : Polynomial A) : Polynomial A × Polynomial A :=
  (p / q, p % q)

end Poly

end Sigma.DSL
