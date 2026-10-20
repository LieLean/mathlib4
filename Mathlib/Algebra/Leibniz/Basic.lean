/-
Copyright (c) 2026 Viviana del Barco, Gustavo Infanti, Exequiel Rivas and Paul Schwahn.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas and Paul Schwahn.
-/
module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Leibniz algebras

This file defines Leibniz algebras.  A Leibniz algebra is a non-unital, non-associative ring `A`
     that satisfies `(x * y) * z = (x * z) * y + x * (y * z)` for any `x y z : A`.
    In the literature this is known as the "right Leibniz property"

## References

* https://en.wikipedia.org/wiki/Leibniz_algebra

-/

/-- A Leibniz algebra `A` is one that satisfies `(x * y) * z = (x * z) * y + x * (y * z)`
    for any `x y z : A`. In the literature this is known as the "right Leibniz property". -/
@[mk_iff isLeibniz_iff]
class IsLeibniz (A : Type*) [NonUnitalNonAssocRing A] : Prop where
  leibniz' (x y z : A) : (x * y) * z = (x * z) * y + x * (y * z)

namespace Leibniz

variable {A : Type*} [NonUnitalNonAssocRing A] [IsLeibniz A]

theorem leibniz (x y z : A) : (x * y) * z = (x * z) * y + x * (y * z) :=
  IsLeibniz.leibniz' x y z

theorem mul_left_mul (x y z : A) : x * (y * z) = (x * y) * z - (x * z) * y := by
  rw [leibniz]
  simp only [add_sub_cancel_left]

theorem mul_left_mul_self (x z : A) : z * (x * x) = 0 := by
  rw [mul_left_mul]
  simp only [sub_self]

theorem mul_left_mul_anticomm (x y z : A) : x * (y * z) = - (x * (z * y)) := by
  rw [mul_left_mul, mul_left_mul]
  simp only [neg_sub]

end Leibniz
