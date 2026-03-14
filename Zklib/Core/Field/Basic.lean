import Mathlib.Algebra.Ring.Basic

universe u

namespace Zklib.Core

/--
A small commutative-ring-shaped signature.

The original `PrimeField*` naming overstated what this layer actually records.
At this point we are only packaging additive and multiplicative operations plus
their basic interaction laws, without characteristic, finiteness, or
multiplicative inverses.
-/
structure CommRingSkeleton where
  Carrier : Type u
  zero : Carrier
  one : Carrier
  add : Carrier -> Carrier -> Carrier
  mul : Carrier -> Carrier -> Carrier
  neg : Carrier -> Carrier

/--
An explicit commutative-ring law package over `CommRingSkeleton`.

This stays operational rather than typeclass-driven, but the name is now
honest about what is and is not recorded at this layer.
-/
structure CommRingLaws extends CommRingSkeleton where
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  neg_add_cancel : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one

namespace CommRingLaws

/--
Bridge a `mathlib` commutative ring into the local operational skeleton.

This gives the custom algebra layer a concrete connection back to the same
`CommRing` instances used by the polynomial and NTT layers.
-/
def ofType (R : Type u) [CommRing R] [Nontrivial R] : CommRingLaws where
  Carrier := R
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  add_assoc := by intro a b c; exact _root_.add_assoc a b c
  add_comm := by intro a b; exact _root_.add_comm a b
  zero_add := by intro a; exact _root_.zero_add a
  neg_add_cancel := by intro a; exact _root_.neg_add_cancel a
  mul_assoc := by intro a b c; exact _root_.mul_assoc a b c
  mul_comm := by intro a b; exact _root_.mul_comm a b
  one_mul := by intro a; exact _root_.one_mul a
  left_distrib := by intro a b c; exact _root_.mul_add a b c
  zero_ne_one := _root_.zero_ne_one

end CommRingLaws

end Zklib.Core
