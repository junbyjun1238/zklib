namespace Zklib.Core

/--
A minimal operational signature for prime-field level structure.

This stays intentionally small until the repository decides how much of the
eventual algebraic hierarchy should come from local interfaces versus mathlib.
-/
structure PrimeFieldOps where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier -> Carrier -> Carrier
  mul : Carrier -> Carrier -> Carrier
  neg : Carrier -> Carrier

/--
An initial law layer for prime-field operations.

This is intentionally still operational rather than typeclass-driven: it gives
the repository a reusable theorem boundary for field-style algebra before we
decide how aggressively to lean on `mathlib` classes in higher layers.
-/
structure PrimeFieldLaws extends PrimeFieldOps where
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  neg_add_cancel : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one

end Zklib.Core
