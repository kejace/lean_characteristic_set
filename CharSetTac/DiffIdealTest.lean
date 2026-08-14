import CharSetTac.DiffIdeal

/-! Worked instances of the certification machinery, so it is demonstrated rather than
merely defined. -/

open scoped Differential

namespace Wu

variable {R : Type*} [CommRing R] [Differential R]

/-- A certificate with a single term gives membership in the saturation.

Here `A = {a}`, the certificate is `H * g = c * δ¹(a)`, i.e. one prolongation. -/
example (a c g H : R) (hcert : H * g = c * (a)′) :
    g ∈ sat (diffIdeal {a}) H := by
  refine mem_sat_of_certificate (Finset.range 1) (fun _ => c) (fun _ => a) (fun _ => 1)
    (by intro i _; rfl) ?_
  simpa [dnth, Function.iterate_one] using hcert

/-- The exponential relation, certified as ideal membership rather than as an equation:
from `y′ - y = 0`, the element `y″ - y` lies in the differential ideal it generates. -/
example (y : R) : (y′)′ - y ∈ diffIdeal ({y′ - y} : Set R) := by
  have h1 : y′ - y ∈ diffIdeal ({y′ - y} : Set R) := self_mem_diffIdeal _ rfl
  have h2 : (y′ - y)′ ∈ diffIdeal ({y′ - y} : Set R) := diffIdeal_deriv_mem h1
  have key : (y′)′ - y = (y′ - y)′ + (y′ - y) := by rw [map_sub]; ring
  rw [key]
  exact (diffIdeal _).add_mem h2 h1

/-- Ideal equality from mutual membership: if the chain and the inputs each lie in the
other's saturation, the saturated differential ideals agree. -/
example (A C H : R) (hAC : A ∈ sat (diffIdeal ({C} : Set R)) H)
    (hCA : C ∈ sat (diffIdeal ({A} : Set R)) H) :
    sat (diffIdeal ({A} : Set R)) H = sat (diffIdeal ({C} : Set R)) H :=
  sat_diffIdeal_eq_of_mem (by rintro x rfl; exact hAC) (by rintro x rfl; exact hCA)

/-- Saturation really is weaker than membership: anything in the ideal is in the
saturation. -/
example (S : Set R) (h x : R) (hx : x ∈ diffIdeal S) : x ∈ sat (diffIdeal S) h :=
  le_sat _ _ hx

end Wu
