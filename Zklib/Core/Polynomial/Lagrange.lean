import Mathlib.LinearAlgebra.Lagrange
import Zklib.Core.Polynomial.Interpolation
import Zklib.Core.Polynomial.Zerofier
import Zklib.Core.EvaluationDomain.Lemmas

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

namespace LagrangeFacts

variable {F : Type*} [Field F]
variable {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι -> F}

theorem nodal_dvd_of_eval_eq_zero (hvs : Set.InjOn v (↑s : Set ι))
    {p : Polynomial F} (hzero : ∀ i ∈ s, p.eval (v i) = 0) :
    _root_.Lagrange.nodal s v ∣ p := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty =>
      simp [_root_.Lagrange.nodal_empty]
  | @insert i s hi IH =>
      have hrooti : p.IsRoot (v i) := hzero i (by simp)
      have hlin : Polynomial.X - Polynomial.C (v i) ∣ p := (Polynomial.dvd_iff_isRoot).2 hrooti
      rcases hlin with ⟨q, hq⟩
      have hs_inj : Set.InjOn v (↑s : Set ι) := by
        intro a ha b hb hab
        exact hvs (by simp [ha]) (by simp [hb]) hab
      have hqzero : ∀ j ∈ s, q.eval (v j) = 0 := by
        intro j hj
        have hpj : p.eval (v j) = 0 := hzero j (by simp [hj])
        have hvji : v j ≠ v i := by
          intro hv
          have hji : j = i := hvs (by simp [hj]) (by simp) hv
          exact hi (hji ▸ hj)
        have hmul : (v j - v i) * q.eval (v j) = 0 := by
          rw [hq] at hpj
          simpa [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hpj
        exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hvji)
      rcases IH hs_inj hqzero with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      calc
        p = (Polynomial.X - Polynomial.C (v i)) * q := hq
        _ = (Polynomial.X - Polynomial.C (v i)) * (_root_.Lagrange.nodal s v * r) := by rw [hr]
        _ = ((Polynomial.X - Polynomial.C (v i)) * _root_.Lagrange.nodal s v) * r := by rw [mul_assoc]
        _ = _root_.Lagrange.nodal (insert i s) v * r := by
              rw [(_root_.Lagrange.nodal_insert_eq_nodal (s := s) (v := v) hi).symm]

end LagrangeFacts

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

theorem nodal_dvd_of_vanishes {poly : Polynomial F}
    (hvanish : (PolynomialSpec.mathlib F).vanishesOn poly domain) :
    Lagrange.nodal (Finset.univ : Finset (Fin domain.size)) domain.point ∣ poly := by
  simpa [PolynomialSpec.mathlib, PolynomialSpec.vanishesOn] using
    (LagrangeFacts.nodal_dvd_of_eval_eq_zero
      (s := (Finset.univ : Finset (Fin domain.size)))
      (v := domain.point)
      domain.point_injOn_univ
      (fun i _ => hvanish i))

end EvaluationDomain

namespace CosetEvaluationDomain

variable {F : Type*} [Field F]

/--
The Lagrange basis polynomial attached to the `i`-th point of a shifted coset
evaluation domain.
-/
def lagrangeBasis (domain : CosetEvaluationDomain F) (i : Fin domain.base.size) : Polynomial F :=
  Lagrange.basis (Finset.univ : Finset (Fin domain.base.size)) domain.point i

theorem eval_lagrangeBasis_self (domain : CosetEvaluationDomain F) (i : Fin domain.base.size) :
    (domain.lagrangeBasis i).eval (domain.point i) = 1 := by
  simpa [lagrangeBasis] using
    (Lagrange.eval_basis_self
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      (i := i)
      domain.point_injOn_univ
      (by simp))

theorem eval_lagrangeBasis_of_ne (domain : CosetEvaluationDomain F) {i j : Fin domain.base.size}
    (hij : i ≠ j) :
    (domain.lagrangeBasis i).eval (domain.point j) = 0 := by
  simpa [lagrangeBasis] using
    (Lagrange.eval_basis_of_ne
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      (i := i)
      (j := j)
      hij
      (by simp))

/--
The Lagrange basis attached to a coset evaluation domain sums to the constant
polynomial `1`.
-/
theorem sum_lagrangeBasis (domain : CosetEvaluationDomain F) :
    (Finset.univ.sum fun i : Fin domain.base.size => domain.lagrangeBasis i) = 1 := by
  simpa [lagrangeBasis] using
    (Lagrange.sum_basis
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      domain.point_injOn_univ
      (by
        refine ⟨⟨0, domain.base.size_pos⟩, by simp⟩))

theorem nodal_dvd_of_vanishes {poly : Polynomial F}
    (hvanish : (PolynomialSpec.mathlib F).vanishesOnCoset poly domain) :
    Lagrange.nodal (Finset.univ : Finset (Fin domain.base.size)) domain.point ∣ poly := by
  simpa [PolynomialSpec.mathlib, PolynomialSpec.vanishesOnCoset] using
    (LagrangeFacts.nodal_dvd_of_eval_eq_zero
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      domain.point_injOn_univ
      (fun i _ => hvanish i))

end CosetEvaluationDomain

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

@[simp] theorem zerofier_eq_nodal {F : Type*} [Field F]
    (domain : EvaluationDomain F) :
    ((mathlib F).zerofier domain : Polynomial F) =
      Lagrange.nodal (Finset.univ : Finset (Fin domain.size)) domain.point := by
  rfl

theorem dvd_of_vanishes {F : Type*} [Field F]
    (domain : EvaluationDomain F) {poly : Polynomial F}
    (hvanish : (PolynomialSpec.mathlib F).vanishesOn poly domain) :
    let zerofier : Polynomial F := (mathlib F).zerofier domain
    zerofier ∣ poly := by
  dsimp [mathlib]
  exact EvaluationDomain.nodal_dvd_of_vanishes (domain := domain) hvanish

theorem vanishingDivisibility {F : Type*} [Field F] :
    @VanishingDivisibility F inferInstance inferInstance
      (mathlib F) (inferInstance : Dvd (Polynomial F)) := by
  intro domain poly hvanish
  exact dvd_of_vanishes domain hvanish

end ZerofierSpec

namespace CosetZerofierSpec

/--
Concrete coset zerofier package given by the nodal polynomial of the shifted
evaluation domain.
-/
def mathlib (F : Type*) [Field F] : CosetZerofierSpec F where
  toPolynomialSpec := PolynomialSpec.mathlib F
  zerofier := fun domain =>
    Lagrange.nodal (Finset.univ : Finset (Fin domain.base.size)) domain.point
  zerofier_vanishes := by
    intro domain i
    simpa [PolynomialSpec.mathlib, PolynomialSpec.vanishesOnCoset] using
      (Lagrange.eval_nodal_at_node
        (s := (Finset.univ : Finset (Fin domain.base.size)))
        (v := domain.point)
        (i := i)
        (by simp))

theorem eval_zerofier {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) (x : F) :
    ((mathlib F).zerofier domain).eval x =
      Finset.univ.prod (fun i : Fin domain.base.size => x - domain.point i) := by
  simpa [mathlib] using
    (Lagrange.eval_nodal
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      (x := x))

theorem degree_zerofier {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) :
    ((mathlib F).zerofier domain).degree = domain.base.size := by
  change (Lagrange.nodal (Finset.univ : Finset (Fin domain.base.size)) domain.point).degree =
      domain.base.size
  convert
    (Lagrange.degree_nodal
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)) using 1
  simp

@[simp] theorem zerofier_eq_nodal {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) :
    ((mathlib F).zerofier domain : Polynomial F) =
      Lagrange.nodal (Finset.univ : Finset (Fin domain.base.size)) domain.point := by
  rfl

theorem dvd_of_vanishes {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) {poly : Polynomial F}
    (hvanish : (PolynomialSpec.mathlib F).vanishesOnCoset poly domain) :
    let zerofier : Polynomial F := (mathlib F).zerofier domain
    zerofier ∣ poly := by
  dsimp [mathlib]
  exact CosetEvaluationDomain.nodal_dvd_of_vanishes (domain := domain) hvanish

theorem vanishingDivisibility {F : Type*} [Field F] :
    @VanishingDivisibility F inferInstance inferInstance
      (mathlib F) (inferInstance : Dvd (Polynomial F)) := by
  intro domain poly hvanish
  exact dvd_of_vanishes domain hvanish

end CosetZerofierSpec

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

namespace CosetInterpolationSpec

/--
Concrete interpolation package using `mathlib`'s Lagrange interpolation over
the canonical nodes of a shifted coset domain.
-/
def mathlib (F : Type*) [Field F] : CosetInterpolationSpec F where
  toPolynomialSpec := PolynomialSpec.mathlib F
  interpolate := fun domain values =>
    Lagrange.interpolate (Finset.univ : Finset (Fin domain.base.size)) domain.point values
  interpolate_spec := by
    intro domain values i
    simpa [PolynomialSpec.mathlib, PolynomialSpec.InterpolatesOnCoset] using
      (Lagrange.eval_interpolate_at_node
        (s := (Finset.univ : Finset (Fin domain.base.size)))
        (v := domain.point)
        (r := values)
        (i := i)
        domain.point_injOn_univ
        (by simp))

theorem degree_interpolate_lt {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) (values : Fin domain.base.size -> F) :
    ((mathlib F).interpolate domain values).degree < domain.base.size := by
  simpa [mathlib] using
    (Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      (r := values)
      domain.point_injOn_univ)

theorem eq_interpolate {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) {poly : Polynomial F}
    (hdeg : poly.degree < domain.base.size) :
    poly = (mathlib F).interpolate domain (fun i => poly.eval (domain.point i)) := by
  have hdeg' : poly.degree < (Finset.univ : Finset (Fin domain.base.size)).card := by
    simpa using hdeg
  simpa [mathlib] using
    (Lagrange.eq_interpolate
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      (f := poly)
      domain.point_injOn_univ
      hdeg')

theorem eq_interpolate_of_eval_eq {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) {values : Fin domain.base.size -> F} {poly : Polynomial F}
    (hdeg : poly.degree < domain.base.size)
    (heval : forall i, poly.eval (domain.point i) = values i) :
    poly = (mathlib F).interpolate domain values := by
  have hdeg' : poly.degree < (Finset.univ : Finset (Fin domain.base.size)).card := by
    simpa using hdeg
  simpa [mathlib] using
    (Lagrange.eq_interpolate_of_eval_eq
      (s := (Finset.univ : Finset (Fin domain.base.size)))
      (v := domain.point)
      (r := values)
      (f := poly)
      domain.point_injOn_univ
      hdeg'
      (by
        intro i hi
        exact heval i))

theorem interpolate_eq_sum_lagrangeBasis {F : Type*} [Field F]
    (domain : CosetEvaluationDomain F) (values : Fin domain.base.size -> F) :
    (mathlib F).interpolate domain values =
      ∑ i : Fin domain.base.size, Polynomial.C (values i) * domain.lagrangeBasis i := by
  rfl

end CosetInterpolationSpec

end Zklib.Core
