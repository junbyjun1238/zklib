import Zklib.Core.Field

namespace Zklib.Core

/--
An operational skeleton for extension-field structure over a lawful base field.

This keeps the representation choices explicit while still recording the basic
embedding and arithmetic operations that later curve and pairing layers will
need.
-/
structure ExtensionFieldSkeleton where
  base : PrimeFieldLaws
  Carrier : Type
  degree : Nat
  embedBase : base.Carrier -> Carrier
  zero : Carrier
  one : Carrier
  add : Carrier -> Carrier -> Carrier
  mul : Carrier -> Carrier -> Carrier
  neg : Carrier -> Carrier

/--
An initial law layer for extension-field operations and the base-field
embedding.
-/
structure ExtensionFieldLaws extends ExtensionFieldSkeleton where
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

end Zklib.Core
