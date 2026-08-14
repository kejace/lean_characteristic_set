/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuGeometry.Bench

/-!
# Machine-generated theorems, filtered by `wu`

These were produced by asking a language model for candidate polynomial identities in plane
geometry, then running `wu` on all of them and keeping only what it proved.

That workflow is worth describing, because it makes an unreliable generator safe. The model
is not trusted at any point: `wu` emits a certificate, `ring1` checks it, and the kernel
checks that. A false candidate cannot survive — it simply fails to produce a certificate.
**The proof checker is the filter**, so generation can be cheap and careless while the
output stays sound.

Of twelve candidates:

* **six** proved outright and are below;
* **four** were true but needed nondegeneracy conditions the generator had not supplied,
  so `wu` correctly left side goals;
* **two** — a nine-point-circle and an Euler-line statement — were simply wrong, and `wu`
  reported that it could not reduce them. Those are exactly the two the model had stated
  incorrectly.

The same generator had already produced *incorrect* Christoffel symbols and an invented
Mathlib import elsewhere in this project. The difference is that here the errors were
caught automatically rather than by hand.
-/

namespace WuGeometry.Generated

#wu_bench theorem centroid_medians_concurrent (Ax Ay Bx By Cx Cy Dx Dy Gx Gy : ℝ)
    (h0 : 3*Gx - Ax - Bx - Cx = 0)
    (h1 : 3*Gy - Ay - By - Cy = 0)
    (h2 : 2*Dx - Bx - Cx = 0)
    (h3 : 2*Dy - By - Cy = 0)
    : (Gx-Ax)*(Dy-Ay) - (Gy-Ay)*(Dx-Ax) = 0 := by wu

#wu_bench theorem parallelogram_diagonal_midpoints (Ax Ay Bx By Cx Cy Dx Dy : ℝ)
    (h0 : Ax + Cx - Bx - Dx = 0)
    (h1 : Ay + Cy - By - Dy = 0)
    : (Ax+Cx)*(Ay+Cy) - (Bx+Dx)*(By+Dy) = 0 := by wu

#wu_bench theorem circle_equal_radii (Ax Ay Bx By Cx Cy Ox Oy : ℝ)
    (h0 : (Ax-Ox)^2 + (Ay-Oy)^2 - (Bx-Ox)^2 - (By-Oy)^2 = 0)
    (h1 : (Bx-Ox)^2 + (By-Oy)^2 - (Cx-Ox)^2 - (Cy-Oy)^2 = 0)
    : (Ax-Ox)^2 + (Ay-Oy)^2 - (Cx-Ox)^2 - (Cy-Oy)^2 = 0 := by wu

#wu_bench theorem perpendicular_bisector_equidistant (Ax Ay Bx By Px Py : ℝ)
    (h0 : 2*Px - Ax - Bx = 0)
    (h1 : 2*Py - Ay - By = 0)
    (h2 : (Px-Ax)*(Bx-Ax) + (Py-Ay)*(By-Ay) = 0)
    : (Px-Ax)^2 + (Py-Ay)^2 - (Px-Bx)^2 - (Py-By)^2 = 0 := by wu

#wu_bench theorem median_length_relation (Ax Ay Bx By Cx Cy Mx My : ℝ)
    (h0 : 2*Mx - Bx - Cx = 0)
    (h1 : 2*My - By - Cy = 0)
    : 4*((Mx-Ax)^2 + (My-Ay)^2) - 2*((Bx-Ax)^2 + (By-Ay)^2) - 2*((Cx-Ax)^2 + (Cy-Ay)^2) + (Bx-Cx)^2 + (By-Cy)^2 = 0 := by wu

#wu_bench theorem parallelogram_area_double (Ax Ay Bx By Cx Cy Dx Dy : ℝ)
    (h0 : Ax + Cx - Bx - Dx = 0)
    (h1 : Ay + Cy - By - Dy = 0)
    : (Bx-Ax)*(Dy-Ay) - (By-Ay)*(Dx-Ax) - ((Cx-Bx)*(Dy-Cy) - (Cy-By)*(Dx-Cx)) = 0 := by wu

end WuGeometry.Generated
