import Jordan.Octonion

/-!
# Octonion cross-term identities for the Albert algebra's Jordan identity

Standalone helper lemmas about four (generically distinct) octonions, needed by
`jordan_case_off01`/`off02`/`off12` in `Jordan.AlbertAlgebra`. Split out from `AlbertAlgebra.lean`
purely to keep that file's size manageable, even though these facts are only ever used there.

Unlike the diagonal cases (`jordan_case_diag0/1/2`), which only ever combine a single
off-diagonal entry with itself (via `mul_star_mul_eq_center` and its mirrors), the off-diagonal
generators genuinely mix four independent octonions with no repeated factor -- terms like
`(p * t) * (star q * o)` -- which have no known closed form via `IsAlternative` alone. The
`innerProduct` bilinear form does at least satisfy a clean "adjoint" identity purely from
`re_mul_comm`/`re_mul_mul_eq_re_mul_mul` (no brute force needed), which shrinks the scalar part of
each cross-term identity; what's left after that -- a genuine octonion-*valued* identity in four
variables -- is settled by brute-force real-coordinate expansion (`obtain` down to the `32`
underlying real coordinates, then `ring`), mirroring `Octonion.re_mul_mul_eq_re_mul_mul`'s
technique but at one octonion further.
-/

namespace Octonion

section CrossTerms

variable {R : Type*}
variable [CommRing R] [Invertible (2 : R)] [StarRing R] [TrivialStar R]
variable {a b c : R}

/-- `innerProduct` is additive in its left argument. `innerProduct` is already bundled as a
`LinearMap.BilinForm`, but nothing public unfolds that bilinearity at the term level -- this (and
its three mirrors just below) exist so `jordan_case_off01`/`off02`/`off12` can pre-expand compound
`innerProduct` arguments (like `innerProduct ((r0 + r1) • p + q * star t) o`) via plain `simp`
before calling `cross_off01`, rather than leaving `innerProduct` applied to an unexpanded sum as an
opaque atom that `linear_combination (norm := module)` can never match up. -/
theorem innerProduct_add_left (x y z : Octonion R a b c) :
    innerProduct (x + y) z = innerProduct x z + innerProduct y z := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨x1a, x1b, x1c, x1d⟩ := x1
  obtain ⟨x2a, x2b, x2c, x2d⟩ := x2
  obtain ⟨y1, y2⟩ := y
  obtain ⟨y1a, y1b, y1c, y1d⟩ := y1
  obtain ⟨y2a, y2b, y2c, y2d⟩ := y2
  obtain ⟨z1, z2⟩ := z
  obtain ⟨z1a, z1b, z1c, z1d⟩ := z1
  obtain ⟨z2a, z2b, z2c, z2d⟩ := z2
  simp [innerProduct_apply, mul_fst, star_fst, star_snd,
    QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
    QuaternionAlgebra.star_mk, smul_eq_mul]

/-- `innerProduct` is `R`-homogeneous in its left argument, the `smul` counterpart to
`innerProduct_add_left`. -/
theorem innerProduct_smul_left (r : R) (x z : Octonion R a b c) :
    innerProduct (r • x) z = r * innerProduct x z := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨x1a, x1b, x1c, x1d⟩ := x1
  obtain ⟨x2a, x2b, x2c, x2d⟩ := x2
  obtain ⟨z1, z2⟩ := z
  obtain ⟨z1a, z1b, z1c, z1d⟩ := z1
  obtain ⟨z2a, z2b, z2c, z2d⟩ := z2
  simp [innerProduct_apply, mul_fst, star_fst, star_snd,
    QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
    QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]

/-- The `innerProduct_add_left` mirror for the right argument, via `innerProduct_comm`. -/
theorem innerProduct_add_right (x y z : Octonion R a b c) :
    innerProduct x (y + z) = innerProduct x y + innerProduct x z := by
  rw [innerProduct_comm x (y + z), innerProduct_add_left, innerProduct_comm y x,
    innerProduct_comm z x]

/-- The `innerProduct_smul_left` mirror for the right argument, via `innerProduct_comm`. -/
theorem innerProduct_smul_right (r : R) (x z : Octonion R a b c) :
    innerProduct x (r • z) = r * innerProduct x z := by
  rw [innerProduct_comm x (r • z), innerProduct_smul_left, innerProduct_comm z x]

/-- `innerProduct` is "self-adjoint" with respect to left multiplication: `⟨x*y, z⟩ = ⟨x, z*ȳ⟩`.
Purely a consequence of `re_mul_mul_eq_re_mul_mul` (applied to both cross terms of
`innerProduct_apply`'s polarization), no brute-force coordinate expansion needed. -/
theorem innerProduct_mul_right (x y z : Octonion R a b c) :
    innerProduct (x * y) z = innerProduct x (z * star y) := by
  simp only [innerProduct_apply, star_mul, star_star]
  congr 1
  show ((x * y) * star z).1.re + (z * (star y * star x)).1.re =
      (x * (y * star z)).1.re + ((z * star y) * star x).1.re
  rw [re_mul_mul_eq_re_mul_mul x y (star z), re_mul_mul_eq_re_mul_mul z (star y) (star x)]

/-- The mirror of `innerProduct_mul_right`, adjoint with respect to right multiplication instead:
`⟨x*y, z⟩ = ⟨y, x̄*z⟩`. Needs `re_mul_comm` in addition to `re_mul_mul_eq_re_mul_mul`, since the
factor being pulled out is on the *outside* of the product rather than matching
`re_mul_mul_eq_re_mul_mul`'s shape directly. -/
theorem innerProduct_mul_left (x y z : Octonion R a b c) :
    innerProduct (x * y) z = innerProduct y (star x * z) := by
  simp only [innerProduct_apply, star_mul, star_star]
  congr 1
  show ((x * y) * star z).1.re + (z * (star y * star x)).1.re =
      (y * (star z * x)).1.re + ((star x * z) * star y).1.re
  rw [re_mul_comm (x * y) (star z), ← re_mul_mul_eq_re_mul_mul (star z) x y,
    re_mul_comm (star z * x) y, re_mul_comm z (star y * star x),
    re_mul_mul_eq_re_mul_mul (star y) (star x) z, re_mul_comm (star y) (star x * z)]

set_option maxHeartbeats 4000000 in
/-- The genuine octonion-*valued* residue of `jordan_case_off01`'s `(0,1)`/`(1,0)` matrix entry,
after `innerProduct_mul_right` has already simplified away the compound arguments
`q * star t`/`t * star q` from the scalar part (see `cross_off01`, which restates this with those
compound forms to match what `jordan_case_off01` actually produces). What's left mixes `p`, `q`,
`t`, `o` with no repeated factor, so `IsAlternative` alone can't close it -- settled directly by
`obtain`-ing all four octonions down to their `32` real coordinates and calling `ring`. -/
lemma cross_off01_core (p q t o : Octonion R a b c) :
    (innerProduct p o + innerProduct (star p) (star o)) • (q * star t) +
        (⅟2 : R) • ((p * t) * (star q * o)) + (⅟2 : R) • ((o * t) * (star q * p)) =
      (innerProduct q (o * t) + innerProduct t (star o * q)) • p +
        (⅟2 : R) • (q * ((star t * star p) * o)) + (⅟2 : R) • ((o * (star p * q)) * star t) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨p1a, p1b, p1c, p1d⟩ := p1
  obtain ⟨p2a, p2b, p2c, p2d⟩ := p2
  obtain ⟨q1, q2⟩ := q
  obtain ⟨q1a, q1b, q1c, q1d⟩ := q1
  obtain ⟨q2a, q2b, q2c, q2d⟩ := q2
  obtain ⟨t1, t2⟩ := t
  obtain ⟨t1a, t1b, t1c, t1d⟩ := t1
  obtain ⟨t2a, t2b, t2c, t2d⟩ := t2
  obtain ⟨o1, o2⟩ := o
  obtain ⟨o1a, o1b, o1c, o1d⟩ := o1
  obtain ⟨o2a, o2b, o2c, o2d⟩ := o2
  apply Octonion.ext
  · apply QuaternionAlgebra.ext
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_fst, add_fst, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_fst, add_fst, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_fst, add_fst, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_fst, add_fst, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring
  · apply QuaternionAlgebra.ext
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_snd, add_snd, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_snd, add_snd, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_snd, add_snd, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring
    · simp [mul_fst, mul_snd, star_fst, star_snd, smul_snd, add_snd, innerProduct_apply,
        QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_sub_mk,
        QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
      ring

/-- `cross_off01_core`, restated with the compound scalar arguments `innerProduct (q * star t) o`/
`innerProduct (t * star q) (star o)` that `jordan_case_off01` actually produces (via
`buildThreeH_mul_general`) rather than the simplified `innerProduct q (o * t)`/
`innerProduct t (star o * q)` forms -- bridged by `innerProduct_mul_right`, no further computation
needed. -/
lemma cross_off01 (p q t o : Octonion R a b c) :
    (innerProduct p o + innerProduct (star p) (star o)) • (q * star t) +
        (⅟2 : R) • ((p * t) * (star q * o)) + (⅟2 : R) • ((o * t) * (star q * p)) =
      (innerProduct (q * star t) o + innerProduct (t * star q) (star o)) • p +
        (⅟2 : R) • (q * ((star t * star p) * o)) + (⅟2 : R) • ((o * (star p * q)) * star t) := by
  rw [innerProduct_mul_right q (star t) o, innerProduct_mul_right t (star q) (star o), star_star,
    star_star]
  exact cross_off01_core p q t o

omit [Invertible (2 : R)] in
/-- `(x * star x).1.re`, unfolded to the same `(star x.1 * x.1).re + c * (star x.2 * x.2).re` form
`mul_mul_star_eq_center`/`mul_star_mul_eq_center` already produce, so those two forms can be
matched up by `rw` without pulling in `OctonionMatrix`'s `diag_just_11`. -/
private theorem re_mul_star_self (x : Octonion R a b c) :
    (x * star x).1.re = (star x.1 * x.1).re + c * (star x.2 * x.2).re := by
  rw [mul_star_self_eq_scalarEmbed]
  simp [scalarEmbed_fst]

/-- The `jordan_case_off01`/`off02`/`off12` diagonal entries need one more cross-term fact beyond
`cross_off01`: `⟨x*y, z*y⟩ = ⟨y*star y⟩ • ⟨x,z⟩` (writing `⟨y*star y⟩` for its real coefficient).
Follows from `innerProduct_mul_right` (peeling the shared `y` off the left) and
`mul_mul_star_eq_center` (collapsing the resulting `(z*y)*star y` sandwich), no brute force. -/
theorem innerProduct_mul_mul_star (x y z : Octonion R a b c) :
    innerProduct (x * y) (z * y) = (y * star y).1.re * innerProduct x z := by
  rw [innerProduct_mul_right x y (z * y), mul_mul_star_eq_center, innerProduct_smul_right,
    re_mul_star_self]

/-- The mirror cross-term fact to `innerProduct_mul_mul_star`, for the other way a repeated factor
`y` can sandwich a `star x`: `⟨y, z*(star x*y)⟩ = ⟨y*star y⟩ • ⟨x,z⟩`. Follows from
`innerProduct_comm`/`innerProduct_mul_right` (peeling `y` off, via the right this time) and
`mul_star_mul_eq_center`. -/
theorem innerProduct_conj_sandwich (x y z : Octonion R a b c) :
    innerProduct y (z * (star x * y)) = (y * star y).1.re * innerProduct x z := by
  rw [innerProduct_comm y (z * (star x * y)), innerProduct_mul_right z (star x * y) y, star_mul,
    star_star, mul_star_mul_eq_center, innerProduct_smul_right, innerProduct_comm z x,
    re_mul_star_self]

lemma off01_entry01 (r0 r1 r2 : R) (p q t o : Octonion R a b c) :
    (⅟2 : R) •
          (r0 * r0 + (p * star p).1.re + (q * star q).1.re +
              (r1 * r1 + (star p * p).1.re + (t * star t).1.re)) •
            (⅟2 : R) • (r0 + r1) • o +
        ((⅟2 : R) • ((innerProduct p) o + (innerProduct (star p)) (star o)) • (r0 + r1) • p +
          (⅟2 : R) • ((innerProduct p) o + (innerProduct (star p)) (star o)) • (q * star t)) +
      (⅟2 : R) • (((r0 + r2) • q + p * t) * (⅟2 : R) • (star q * o)) +
      (⅟2 : R) • ((⅟2 : R) • (o * t) * ((r1 + r2) • star t + star q * p)) =
    (⅟2 : R) •
          (r0 + r1) •
            (⅟2 : R) •
              (r0 * r0 + (p * star p).1.re + (q * star q).1.re +
                  (r1 * r1 + (star p * p).1.re + (t * star t).1.re)) •
                o +
        (⅟2 : R) •
          ((r0 + r1) * (innerProduct p) o + (innerProduct (q * star t)) o +
              ((r0 + r1) * (innerProduct (star p)) (star o) + (innerProduct (t * star q)) (star o))) •
            p +
      (⅟2 : R) • (q * (⅟2 : R) • (((r0 + r2) • star q + star t * star p) * o)) +
      (⅟2 : R) • ((⅟2 : R) • (o * ((r1 + r2) • t + star p * q)) * star t) := by
  linear_combination
    (norm := (simp only [smul_smul, mul_add, add_mul, smul_add, add_smul, mul_smul_comm,
      smul_mul_assoc]; ring_nf; abel))
    (⅟2 : R) • cross_off01 p q t o

/-- The `(0,0)` matrix-entry identity `jordan_case_off01` needs, stated at the `R` level (i.e.
after `jordan_case_off01` has already peeled off the shared `scalarEmbed` via
`simp only [← map_mul, ← map_add]; congr 1`). The two cross-terms `⟨p*t, o*t⟩`/`⟨q, o*(star p*q)⟩`
are exactly `innerProduct_mul_mul_star`/`innerProduct_conj_sandwich` (each specialized so the
repeated factor is `t`/`q` respectively), collapsing them to multiples of `⟨p,o⟩`; everything left
is then a plain `ring` identity. -/
theorem off01_entry00 (r0 r1 r2 : R) (p q t o : Octonion R a b c) :
    (r0 * r0 + (p * star p).1.re + (q * star q).1.re) * (innerProduct p) o +
        (⅟2 : R) * ((r0 + r1) * ((r0 + r1) * (innerProduct p) o + (innerProduct (q * star t)) o)) +
      (⅟2 : R) * ((r0 + r2) * (innerProduct q) (o * t) + (innerProduct (p * t)) (o * t)) =
    r0 * ((r0 + r1) * (innerProduct p) o + (innerProduct (q * star t)) o) +
        (⅟2 : R) *
          ((r0 * r0 + (p * star p).1.re + (q * star q).1.re +
              (r1 * r1 + (star p * p).1.re + (t * star t).1.re)) *
            (innerProduct p) o) +
      (⅟2 : R) * (innerProduct q) (o * ((r1 + r2) • t + star p * q)) := by
  rw [show o * ((r1 + r2) • t + star p * q) = (r1 + r2) • (o * t) + o * (star p * q) from by
      rw [mul_add, mul_smul_comm],
    innerProduct_add_right, innerProduct_smul_right,
    show innerProduct (p * t) (o * t) = (t * star t).1.re * innerProduct p o from
      innerProduct_mul_mul_star p t o,
    show innerProduct q (o * (star p * q)) = (q * star q).1.re * innerProduct p o from
      innerProduct_conj_sandwich p q o,
    show (p * star p).1.re = (star p * p).1.re from by
      rw [mul_star_self_eq_scalarEmbed, star_mul_self_eq_scalarEmbed],
    show innerProduct (q * star t) o = innerProduct q (o * t) from by
      rw [innerProduct_mul_right q (star t) o, star_star]]
  linear_combination
    (r0 * (innerProduct q) (o * t) - (star p * p).1.re * (innerProduct p) o -
        (q * star q).1.re * (innerProduct p) o + r0 * (innerProduct p) o * r1) *
      mul_invOf_self (2 : R)

/-- The `(1,1)` matrix-entry identity `jordan_case_off01` needs -- the `off01_entry00` mirror for
`r1`/`star p`/`star o` in place of `r0`/`p`/`o`, using `innerProduct_conj_sandwich (star p) t
(star o)` and `innerProduct_mul_mul_star (star p) q (star o)` (with `star_star` cleanup) for the
two cross-terms instead. -/
theorem off01_entry11 (r0 r1 r2 : R) (p q t o : Octonion R a b c) :
    (r1 * r1 + (star p * p).1.re + (t * star t).1.re) * (innerProduct (star p)) (star o) +
        (⅟2 : R) *
          ((r0 + r1) * ((r0 + r1) * (innerProduct (star p)) (star o) + (innerProduct (t * star q)) (star o))) +
      (⅟2 : R) * ((r1 + r2) * (innerProduct t) (star o * q) + (innerProduct (star p * q)) (star o * q)) =
    r1 * ((r0 + r1) * (innerProduct (star p)) (star o) + (innerProduct (t * star q)) (star o)) +
        (⅟2 : R) *
          ((r0 * r0 + (p * star p).1.re + (q * star q).1.re +
              (r1 * r1 + (star p * p).1.re + (t * star t).1.re)) *
            (innerProduct (star p)) (star o)) +
      (⅟2 : R) * (innerProduct t) (star o * ((r0 + r2) • q + p * t)) := by
  rw [show star o * ((r0 + r2) • q + p * t) = (r0 + r2) • (star o * q) + star o * (p * t) from by
      rw [mul_add, mul_smul_comm],
    innerProduct_add_right, innerProduct_smul_right,
    show innerProduct t (star o * (p * t)) = (t * star t).1.re * innerProduct (star p) (star o)
      from by
      have h := innerProduct_conj_sandwich (star p) t (star o)
      rwa [star_star] at h,
    show innerProduct (star p * q) (star o * q) = (q * star q).1.re * innerProduct (star p) (star o)
      from innerProduct_mul_mul_star (star p) q (star o),
    show (p * star p).1.re = (star p * p).1.re from by
      rw [mul_star_self_eq_scalarEmbed, star_mul_self_eq_scalarEmbed],
    show innerProduct (t * star q) (star o) = innerProduct t (star o * q) from by
      rw [innerProduct_mul_right t (star q) (star o), star_star]]
  linear_combination
    (r1 * (innerProduct t) (star o * q) - (star p * p).1.re * (innerProduct (star p)) (star o) -
        (t * star t).1.re * (innerProduct (star p)) (star o) +
        r0 * (innerProduct (star p)) (star o) * r1) *
      mul_invOf_self (2 : R)

/-- The `(2,2)` entry of `jordan_case_off01` needs one more bridge: `⟨t, star o * q⟩` and
`⟨q, o * t⟩` are the same value under two layers of `innerProduct_star_star`. -/
theorem innerProduct_swap_bridge (q t o : Octonion R a b c) :
    innerProduct t (star o * q) = innerProduct q (o * t) := by
  rw [innerProduct_comm t (star o * q), innerProduct_mul_right (star o) q t,
    show t * star q = star (q * star t) from by rw [star_mul, star_star],
    innerProduct_star_star, innerProduct_comm o (q * star t), innerProduct_mul_right q (star t) o,
    star_star]

omit [Invertible (2 : R)] in
/-- The `star`-conjugate mirror of `re_mul_star_self`, for `(star x * x).1.re` instead. -/
theorem re_star_mul_self (x : Octonion R a b c) :
    (star x * x).1.re = (star x.1 * x.1).re + c * (star x.2 * x.2).re := by
  rw [star_mul_self_eq_scalarEmbed]
  simp [scalarEmbed_fst]

/-- Mirror of `innerProduct_mul_mul_star` for a repeated factor on the *left* instead of the
right: `⟨y*x, y*z⟩ = ⟨star y*y⟩ • ⟨x,z⟩`. Needed by the `(2,2)` entry below, where the repeated
factor (`star q`/`star t`) sits on the left of both products rather than the right. -/
theorem innerProduct_mul_mul_star_left (x y z : Octonion R a b c) :
    innerProduct (y * x) (y * z) = (star y * y).1.re * innerProduct x z := by
  rw [innerProduct_mul_left y x (y * z), star_mul_mul_eq_center, innerProduct_smul_right,
    re_star_mul_self]

/-- The `(2,2)` matrix-entry identity `jordan_case_off01` needs. Unlike `(0,0)`/`(1,1)`, the
`diag2` slot of `buildThreeH_mul_general` has no `r2*s2` term at all (`offPiece01`'s own `s2 = 0`),
so this is *purely* the two cross-terms -- but here, unlike the other entries, `simp`'s own
reduction leaves everything in `star q`/`star t`/`star o` form rather than simplifying back to
`q`/`t`/`o`, so the two cross-terms need `innerProduct_mul_mul_star_left` (repeated factor on the
left) instead of `innerProduct_mul_mul_star`, plus a small direct bridge (`innerProduct_comm` +
`innerProduct_mul_right`) identifying `⟨star t,star q*o⟩` with `⟨star q,star t*star o⟩`. No
`mul_invOf_self` correction needed. -/
theorem off01_entry22 (r0 r1 r2 : R) (p q t o : Octonion R a b c) :
    (⅟2 : R) * ((r0 + r2) * (innerProduct (star q)) (star t * star o) +
        (innerProduct (star t * star p)) (star t * star o)) +
      (⅟2 : R) * ((r1 + r2) * (innerProduct (star t)) (star q * o) +
        (innerProduct (star q * p)) (star q * o)) =
    (⅟2 : R) * (innerProduct (star q)) (((r1 + r2) • star t + star q * p) * star o) +
      (⅟2 : R) * (innerProduct (star t)) (((r0 + r2) • star q + star t * star p) * o) := by
  rw [show ((r1 + r2) • star t + star q * p) * star o =
        (r1 + r2) • (star t * star o) + (star q * p) * star o from by
      rw [add_mul, smul_mul_assoc],
    show ((r0 + r2) • star q + star t * star p) * o =
        (r0 + r2) • (star q * o) + (star t * star p) * o from by
      rw [add_mul, smul_mul_assoc],
    innerProduct_add_right, innerProduct_smul_right,
    innerProduct_add_right, innerProduct_smul_right,
    show innerProduct (star q) ((star q * p) * star o) = (q * star q).1.re * innerProduct p o
      from by
      rw [innerProduct_comm (star q) ((star q * p) * star o),
        innerProduct_mul_right (star q * p) (star o) (star q), star_star,
        innerProduct_mul_mul_star_left p (star q) o, star_star],
    show innerProduct (star t) ((star t * star p) * o) =
        (t * star t).1.re * innerProduct (star p) (star o) from by
      rw [innerProduct_comm (star t) ((star t * star p) * o),
        innerProduct_mul_right (star t * star p) o (star t),
        innerProduct_mul_mul_star_left (star p) (star t) (star o), star_star],
    show innerProduct (star t * star p) (star t * star o) =
        (t * star t).1.re * innerProduct (star p) (star o) from by
      rw [innerProduct_mul_mul_star_left (star p) (star t) (star o), star_star],
    show innerProduct (star q * p) (star q * o) = (q * star q).1.re * innerProduct p o from by
      rw [innerProduct_mul_mul_star_left p (star q) o, star_star],
    show innerProduct (star t) (star q * o) = innerProduct (star q) (star t * star o) from by
      rw [innerProduct_comm (star t) (star q * o), innerProduct_mul_right (star q) o (star t)]]
  ring

end CrossTerms

end Octonion
