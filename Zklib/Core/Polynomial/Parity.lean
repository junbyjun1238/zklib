import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions

open scoped Polynomial

namespace Zklib.Core

namespace PolynomialParity

variable {R : Type*} [CommSemiring R]

/--
The even-index coefficient subpolynomial of `p`.
-/
noncomputable def evenPart (p : R[X]) : R[X] :=
  Polynomial.contract 2 p

/--
The odd-index coefficient subpolynomial of `p`.
-/
noncomputable def oddPart (p : R[X]) : R[X] :=
  Polynomial.contract 2 (Polynomial.divX p)

theorem coeff_evenPart (p : R[X]) (n : Nat) :
    (evenPart p).coeff n = p.coeff (2 * n) := by
  simpa [evenPart, Nat.mul_comm] using
    (Polynomial.coeff_contract (p := 2) (by decide : 2 ≠ 0) p n)

theorem coeff_oddPart (p : R[X]) (n : Nat) :
    (oddPart p).coeff n = p.coeff (2 * n + 1) := by
  rw [oddPart, Polynomial.coeff_contract (p := 2) (by decide : 2 ≠ 0)]
  simp [Polynomial.coeff_divX, Nat.mul_comm, Nat.add_comm]

/--
Coefficient-level radix-2 decomposition of a polynomial.
-/
theorem expand_evenPart_add_X_mul_expand_oddPart (p : R[X]) :
    Polynomial.expand R 2 (evenPart p) + Polynomial.X * Polynomial.expand R 2 (oddPart p) = p := by
  apply Polynomial.ext
  intro n
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · rw [hk, Polynomial.coeff_add, Polynomial.coeff_expand_mul' (p := 2) (by decide : 0 < 2)]
    rw [coeff_evenPart]
    cases k with
    | zero =>
        simp
    | succ k =>
        have hk' : 2 * Nat.succ k = (2 * k + 1) + 1 := by
          calc
            2 * Nat.succ k = 2 * k + 2 := by rw [Nat.mul_succ]
            _ = (2 * k + 1) + 1 := by simp [Nat.add_assoc]
        rw [hk', Polynomial.coeff_X_mul, Polynomial.coeff_expand (p := 2) (by decide : 0 < 2)]
        simp
  · rw [hk, Polynomial.coeff_add, Polynomial.coeff_expand (p := 2) (by decide : 0 < 2)]
    have hk' : 2 * k + 1 = (2 * k) + 1 := by simp
    rw [hk', Polynomial.coeff_X_mul, Polynomial.coeff_expand_mul' (p := 2) (by decide : 0 < 2)]
    rw [coeff_oddPart]
    simp

/--
Standard radix-2 polynomial decomposition:
`p(X) = evenPart(p)(X^2) + X * oddPart(p)(X^2)`.
-/
theorem evenPart_comp_X_sq_add_X_mul_oddPart_comp_X_sq (p : R[X]) :
    (evenPart p).comp (Polynomial.X ^ 2) + Polynomial.X * (oddPart p).comp (Polynomial.X ^ 2) = p := by
  simpa [Polynomial.expand_eq_comp_X_pow] using
    (expand_evenPart_add_X_mul_expand_oddPart (R := R) p)

theorem eval_evenPart_sq_add_oddPart_sq (p : R[X]) (x : R) :
    p.eval x = (evenPart p).eval (x ^ 2) + x * (oddPart p).eval (x ^ 2) := by
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp] using
    congrArg (fun q : R[X] => q.eval x)
      (evenPart_comp_X_sq_add_X_mul_oddPart_comp_X_sq (R := R) p).symm

end PolynomialParity

end Zklib.Core
