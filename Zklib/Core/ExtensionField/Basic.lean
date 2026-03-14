import Mathlib.Algebra.Algebra.Basic
import Zklib.Core.Field

universe u v

namespace Zklib.Core

/--
An operational skeleton for a ring-like scalar extension.

This keeps the representation choices explicit while still recording the basic
embedding and arithmetic operations that later curve and pairing layers will
need.
-/
structure ExtensionAlgebraSkeleton where
  base : CommRingLaws.{u}
  Carrier : Type v
  degree : Nat
  embedBase : base.Carrier -> Carrier
  zero : Carrier
  one : Carrier
  add : Carrier -> Carrier -> Carrier
  mul : Carrier -> Carrier -> Carrier
  neg : Carrier -> Carrier

/--
An initial law layer for extension-ring operations and the base-field
embedding.
-/
structure ExtensionAlgebraLaws extends ExtensionAlgebraSkeleton where
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  neg_add_cancel : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  embedBase_zero : embedBase base.zero = zero
  embedBase_one : embedBase base.one = one
  embedBase_add : ∀ a b, embedBase (base.add a b) = add (embedBase a) (embedBase b)
  embedBase_mul : ∀ a b, embedBase (base.mul a b) = mul (embedBase a) (embedBase b)
  embedBase_neg : ∀ a, embedBase (base.neg a) = neg (embedBase a)

namespace ExtensionAlgebraLaws

/--
Bridge a `mathlib` scalar extension into the local operational skeleton.

The extension degree is supplied explicitly because it is not derivable from a
generic `Algebra` instance alone.
-/
def ofAlgebra (K : Type u) (L : Type v) [CommRing K] [Nontrivial K]
    [CommRing L] [Nontrivial L] [Algebra K L] (degree : Nat) :
    ExtensionAlgebraLaws where
  base := CommRingLaws.ofType K
  Carrier := L
  degree := degree
  embedBase := algebraMap K L
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
  embedBase_zero := by
    simp [CommRingLaws.ofType]
  embedBase_one := by
    simp [CommRingLaws.ofType]
  embedBase_add := by
    intro a b
    simp [CommRingLaws.ofType]
  embedBase_mul := by
    intro a b
    simp [CommRingLaws.ofType]
  embedBase_neg := by
    intro a
    simp [CommRingLaws.ofType]

end ExtensionAlgebraLaws

end Zklib.Core
