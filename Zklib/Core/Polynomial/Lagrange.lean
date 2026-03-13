import Mathlib.LinearAlgebra.Lagrange
import Zklib.Core.Polynomial.Interpolation
import Zklib.Core.Polynomial.Zerofier
import Zklib.Core.Subgroup.Lemmas

noncomputable section

namespace Zklib.Core

open Polynomial

namespace PolynomialSpec

/--
Concrete polynomial model backed by `mathlib`'s `Polynomial`.
-/
def mathlib (F : Type*) [Field F] : PolynomialSpec F where
  Carrier := Polynomial F
  eval poly x := poly.eval x

end PolynomialSpec

namespace EvaluationDomain

variable {F : Type*} [Field F]

/--
The Lagrange basis polynomial attached to the `i`-th point of an evaluation domain.
-/
def lagrangeBasis (domain : EvaluationDomain F) (i : Fin domain.size) : Polynomial F :=
  Lagrange.basis (Finset.univ : Finset (Fin domain.size)) domain.point i

theorem eval_lagrangeBasis_self (domain : EvaluationDomain F) (i : Fin domain.size) :
    (domain.lagrangeBasis i).eval (domain.point i) = 1 := by
  simpa [lagrangeBasis] using
    (Lagrange.eval_basis_self
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      (i := i)
      domain.point_injOn_univ
      (by simp))

theorem eval_lagrangeBasis_of_ne (domain : EvaluationDomain F) {i j : Fin domain.size}
    (hij : i ≠ j) :
    (domain.lagrangeBasis i).eval (domain.point j) = 0 := by
  simpa [lagrangeBasis] using
    (Lagrange.eval_basis_of_ne
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      (i := i)
      (j := j)
      hij
      (by simp))

/--
The Lagrange basis attached to an evaluation domain sums to the constant
polynomial `1`.
-/
theorem sum_lagrangeBasis (domain : EvaluationDomain F) :
    (Finset.univ.sum fun i : Fin domain.size => domain.lagrangeBasis i) = 1 := by
  simpa [lagrangeBasis] using
    (Lagrange.sum_basis
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      domain.point_injOn_univ
      (by
        refine ⟨⟨0, domain.size_pos⟩, by simp⟩))

end EvaluationDomain

namespace ZerofierSpec

/--
Concrete zerofier package given by the nodal polynomial of the evaluation domain.
-/
def mathlib (F : Type*) [Field F] : ZerofierSpec F where
  toPolynomialSpec := PolynomialSpec.mathlib F
  zerofier := fun domain =>
    Lagrange.nodal (Finset.univ : Finset (Fin domain.size)) domain.point
  zerofier_vanishes := by
    intro domain i
    simpa [PolynomialSpec.mathlib, PolynomialSpec.vanishesOn] using
      (Lagrange.eval_nodal_at_node
        (s := (Finset.univ : Finset (Fin domain.size)))
        (v := domain.point)
        (i := i)
        (by simp))

theorem eval_zerofier {F : Type*} [Field F]
    (domain : EvaluationDomain F) (x : F) :
    ((mathlib F).zerofier domain).eval x =
      Finset.univ.prod (fun i : Fin domain.size => x - domain.point i) := by
  simpa [mathlib] using
    (Lagrange.eval_nodal
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      (x := x))

theorem degree_zerofier {F : Type*} [Field F]
    (domain : EvaluationDomain F) :
    ((mathlib F).zerofier domain).degree = domain.size := by
  change (Lagrange.nodal (Finset.univ : Finset (Fin domain.size)) domain.point).degree =
      domain.size
  convert
    (Lagrange.degree_nodal
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)) using 1
  simp

end ZerofierSpec

namespace InterpolationSpec

/--
Concrete interpolation package using `mathlib`'s Lagrange interpolation over the
canonical nodes of an evaluation domain.
-/
def mathlib (F : Type*) [Field F] : InterpolationSpec F where
  toPolynomialSpec := PolynomialSpec.mathlib F
  interpolate := fun domain values =>
    Lagrange.interpolate (Finset.univ : Finset (Fin domain.size)) domain.point values
  interpolate_spec := by
    intro domain values i
    simpa [PolynomialSpec.mathlib, PolynomialSpec.InterpolatesOn] using
      (Lagrange.eval_interpolate_at_node
        (s := (Finset.univ : Finset (Fin domain.size)))
        (v := domain.point)
        (r := values)
        (i := i)
        domain.point_injOn_univ
        (by simp))

theorem degree_interpolate_lt {F : Type*} [Field F]
    (domain : EvaluationDomain F) (values : Fin domain.size -> F) :
    ((mathlib F).interpolate domain values).degree < domain.size := by
  simpa [mathlib] using
    (Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      (r := values)
      domain.point_injOn_univ)

theorem eq_interpolate {F : Type*} [Field F]
    (domain : EvaluationDomain F) {poly : Polynomial F}
    (hdeg : poly.degree < domain.size) :
    poly = (mathlib F).interpolate domain (fun i => poly.eval (domain.point i)) := by
  have hdeg' : poly.degree < (Finset.univ : Finset (Fin domain.size)).card := by
    simpa using hdeg
  simpa [mathlib] using
    (Lagrange.eq_interpolate
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      (f := poly)
      domain.point_injOn_univ
      hdeg')

theorem eq_interpolate_of_eval_eq {F : Type*} [Field F]
    (domain : EvaluationDomain F) {values : Fin domain.size -> F} {poly : Polynomial F}
    (hdeg : poly.degree < domain.size)
    (heval : forall i, poly.eval (domain.point i) = values i) :
    poly = (mathlib F).interpolate domain values := by
  have hdeg' : poly.degree < (Finset.univ : Finset (Fin domain.size)).card := by
    simpa using hdeg
  simpa [mathlib] using
    (Lagrange.eq_interpolate_of_eval_eq
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      (r := values)
      (f := poly)
      domain.point_injOn_univ
      hdeg'
      (by
        intro i hi
        exact heval i))

theorem interpolate_eq_sum_lagrangeBasis {F : Type*} [Field F]
    (domain : EvaluationDomain F) (values : Fin domain.size -> F) :
    (mathlib F).interpolate domain values =
      ∑ i : Fin domain.size, Polynomial.C (values i) * domain.lagrangeBasis i := by
  rfl

end InterpolationSpec

end Zklib.Core
