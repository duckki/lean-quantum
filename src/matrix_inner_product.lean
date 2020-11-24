import matrix_lemmas
import algebra.big_operators.default
import analysis.normed_space.inner_product

open_locale big_operators
open Matrix

------------------------------------------------------------------------------
-- Vector inner_product

namespace Matrix

variables {n : ℕ}

noncomputable
def inner_product (x y : Vector n) : ℂ := ((x†) ⬝ y) 0 0

noncomputable
instance has_inner {n} : has_inner ℂ (Vector n) := ⟨inner_product⟩

-- `⟪x, y⟫` : inner product notation.
-- `⟨ , ⟩` is already taken in Lean. So, use  `⟪ , ⟫`, instead.
notation `⟪` X `,` Y `⟫` := @has_inner.inner ℂ _ _ X Y

end Matrix


section inner_product

variables {n : ℕ} {x y z : Vector n}

lemma inner_product_self_eq_sum_conj_mul : ⟪x, x⟫ = ∑ i, ((x i 0)†) * x i 0 := by refl

lemma inner_product_self_eq_sum_norm_sq : ⟪x, x⟫ = ∑ i, (x i 0).norm_sq
:= begin
    rw inner_product_self_eq_sum_conj_mul,
    congr, apply funext, intro i,
    rw is_R_or_C.conj_mul_eq_norm_sq_left,
    simp,
end

@[simp]
lemma re_inner_product_self : (⟪x, x⟫.re : ℂ) = ⟪x, x⟫
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    norm_cast,
end

-- 4. Positive semi-definite or nonnegative-definite
@[simp]
lemma inner_product_self_re_nonneg (x : Vector n) : 0 ≤ ⟪x, x⟫.re
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    rw <- finset.univ.sum_hom complex.re,
    apply finset.sum_nonneg,
    intros i ip, simp,
end

@[simp]
lemma inner_product_self_im_zero (x : Vector n): ⟪x, x⟫.im = 0
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    rw <- finset.univ.sum_hom complex.im,
    apply finset.sum_eq_zero, intros i ip, simp,
end

@[simp]
lemma abs_inner_product_self_eq_re : |⟪x,x⟫| = ⟪x,x⟫.re
:= begin
    simp,
    rw <- re_inner_product_self,
    rw complex.abs_of_nonneg; simp,
end

-- 5. Point-separating or non-degenerate
lemma inner_product_self_zero : ⟪x, x⟫ = 0 → x = 0
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    intros h,

    have h': ∑ (i : fin n), complex.norm_sq (x i 0) = 0, {
        apply_mod_cast h,
    },
    clear h,

    have f1: ∀ i, complex.norm_sq (x i 0) = 0, {
        intro i,
        apply (finset.sum_eq_zero_iff_of_nonneg _).mp h'; simp,
    },

    have f2: ∀ i, x i 0 = 0, {
        intros i,
        apply complex.norm_sq_eq_zero.mp; apply f1,
    },

    apply matrix.ext, intros i j,
    have j0 : j = 0, cases j, simp, cases j0, clear j0, simp,
    apply f2,
end

@[simp]
lemma inner_product_self_neg : ⟪-x, -x⟫ = ⟪x, x⟫
:= begin
    unfold inner Matrix.inner_product,
    rw adjoint_neg, simp,
end

lemma inner_product_self_add : ⟪x+y , x+y⟫ = ⟪x,x⟫ + ⟪x,y⟫ + ⟪y,x⟫ + ⟪y,y⟫
:= begin
    unfold inner Matrix.inner_product,
    rw adjoint_add,
    rw matrix.add_mul,
    iterate 2 { rw matrix.mul_add },
    repeat { rw matrix_add_app },
    simp,
    ring,
end

lemma inner_product_self_re_inj (v : ℝ) : ⟪x,x⟫.re = v → ⟪x,x⟫ = v
:= begin
    intros h,
    ext, {
        rw h, simp,
    }, {
        rw inner_product_self_im_zero, simp,
    }
end

example (v : ℝ) : ⟪x,x⟫ ≠ v → ⟪x,x⟫.re ≠ v
:= by {contrapose!, apply inner_product_self_re_inj}

lemma inner_product_self_re_eq_one_of_unit : x.unit → ⟪x,x⟫.re = 1
:= begin
    intros xu,
    unfold inner Matrix.inner_product,
    rw unfold_unit xu, simp,
end


lemma inner_product_smul_l {s : ℂ} : ⟪s • x, y⟫ = (s†) • ⟪x, y⟫
:= by {unfold inner Matrix.inner_product, simp [adjoint_smul]}

lemma inner_product_smul_r {s : ℂ} : ⟪x, s • y⟫ = s • ⟪x, y⟫
:= by {unfold inner Matrix.inner_product, simp}


lemma inner_product_add_left : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
:= begin
    unfold inner Matrix.inner_product,
    rw adjoint_add,
    rw matrix.add_mul,
    simp,
end

lemma inner_product_add_right : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
:= begin
    unfold inner Matrix.inner_product,
    rw matrix.mul_add,
    simp,
end


@[simp]
lemma conj_inner_product : ⟪y, x⟫† = ⟪x, y⟫
:= begin
    unfold inner Matrix.inner_product,
    unfold matrix.mul matrix.dot_product,
    rw <- complex.conj_sum_dist,
    congr' 1, apply funext, intro i,
    unfold adjoint,
    simp, ring,
end


lemma abs_inner_product_comm : |⟪x, y⟫| = |⟪y, x⟫|
:= begin
    rw <- conj_inner_product,
    rw is_R_or_C.abs_conj,
end

lemma re_inner_product_comm : ⟪x, y⟫.re = ⟪y, x⟫.re
:= begin
    rw <- complex.re_conj_eq_re, simp,
end

lemma inner_product_mul_eq_norm_sq : ⟪x, y⟫ * ⟪y, x⟫ = ⟪y, x⟫.norm_sq
:= begin
    rw <- conj_inner_product,
    rw is_R_or_C.conj_mul_eq_norm_sq_left, simp,
end

@[simp]
lemma inner_product_zero_r : ⟪x,(0 : Vector n)⟫ = 0
:= begin
    unfold inner Matrix.inner_product,
    simp,
end

@[simp]
lemma inner_product_zero_l : ⟪(0 : Vector n),x⟫ = 0
:= begin
    unfold inner Matrix.inner_product,
    rw adjoint_zero, simp,
end


lemma inner_product_zero_iff : x† ⬝ y = 0 ↔ ⟪x,y⟫ = 0
:= begin
    unfold inner Matrix.inner_product, split; intros h, {
        rw h, simp,
    }, {
        apply matrix.ext, intros i j,
        have i0 : i = 0, cases i; simp, cases i0; clear i0,
        have j0 : j = 0, cases j; simp, cases j0; clear j0,
        simp at *, assumption,
    }
end

lemma inner_product_one_iff : x† ⬝ y = 1 ↔ ⟪x,y⟫ = 1
:= begin
    unfold inner Matrix.inner_product, split; intros h, {
        rw h, simp,
    }, {
        apply matrix.ext, intros i j,
        have i0 : i = 0, cases i; simp, cases i0; clear i0,
        have j0 : j = 0, cases j; simp, cases j0; clear j0,
        simp at *, assumption,
    }
end

end inner_product


------------------------------------------------------------------------------
-- norm

namespace Matrix

variables {n : ℕ}
variables (x y : Vector n)

noncomputable
def norm : ℝ := ⟪x,x⟫.re.sqrt

noncomputable
instance : has_norm (Vector n) := ⟨Matrix.norm⟩

-- Use the standard norm notation of ∥x∥

end Matrix


-- Matirx.norm lemmas (not the global `norm`)
section Matrix_norm

variables {n : ℕ} {x y z : Vector n}

@[simp]
lemma Matrix.zero_norm_eq_zero : (0 : Vector n).norm = (0 : ℝ)
:= begin
    unfold Matrix.norm inner Matrix.inner_product, simp,
end

@[simp]
lemma Matrix.norm_neg : (-x).norm = x.norm
:= begin
    unfold Matrix.norm, simp,
end

@[simp]
lemma Matrix.norm_nonneg : 0 ≤ x.norm
:= begin
    unfold Matrix.norm,
    apply real.sqrt_nonneg,
end

end Matrix_norm


-- Global `norm` lemmas
section norm

variables {n : ℕ} {x y z : Vector n}

lemma Matrix.norm_sq_eq_re_inner_product_self : ∥x∥^2 = ⟪x, x⟫.re
:= begin
    unfold norm Matrix.norm,
    rw pow_two,
    rw real.mul_self_sqrt; simp,
end

@[simp]
lemma Matrix.norm_neg' : ∥-x∥ = ∥x∥
:= begin
    unfold norm, simp,
end

@[simp]
lemma Matrix.norm_zero : ∥(0 : Vector n)∥ = 0
:= begin
    unfold norm Matrix.norm, simp,
end

@[simp]
lemma Matrix.norm_nonneg' : 0 ≤ ∥x∥
:= begin
    unfold norm, simp,
end

lemma Matrix.norm_smul (s : ℂ) : ∥s • x∥ = ∥s∥ * ∥x∥
:= begin
    unfold norm Matrix.norm,
    have f1: ∀ (r : ℝ), |s| * r.sqrt = (|s|^2 * r).sqrt, {
        intros r,
        have f2: |s| = (|s|^2).sqrt, {
            rw pow_two, simp,
        },
        rw real.sqrt_mul,
        congr; try {simp},
        apply pow_two_nonneg,
    },
    rw <- is_R_or_C.abs_to_complex,
    rw f1,
    apply (real.sqrt_inj _ _).mpr, {
        rw inner_product_smul_l,
        rw inner_product_smul_r,

        rw <- smul_assoc,

        have f1: (s†) • s = |s|^2, {
            simp,
            norm_cast,
            rw complex.norm_sq_eq_abs,
        },
        rw f1, clear f1,
        have f2: |s| ^ 2 * ⟪x,x⟫.re = (|s| ^ 2 • ⟪x,x⟫).re, {
            simp,
        },
        rw f2,
        congr' 1,
        simp,
        norm_cast,
    }, {
        simp,
    }, {
        apply mul_nonneg; simp,
    },
end

lemma norm_eq_one_of_unit : x.unit → ∥x∥ = 1
:= begin
    intros xu,
    unfold norm Matrix.norm,
    rw inner_product_self_re_eq_one_of_unit xu, simp,
end

end norm


------------------------------------------------------------------------------
-- dist

namespace Matrix

variables {n : ℕ}
variables (x y : Vector n)

noncomputable
def dist := norm (x - y)

noncomputable
instance : has_dist (Vector n) := ⟨Matrix.dist⟩

end Matrix


-- `dist` lemmas
section dist

variables {n : ℕ}
variables {x y z : Vector n}

lemma Matrix.dist_eq (x y : Vector n) : dist x y = ∥x - y∥ := by refl

lemma Matrix.dist_self (x : Vector n) : dist x x = 0
:= begin
    unfold dist has_dist.dist Matrix.dist, simp,
end

@[simp]
lemma Matrix.dist_nonneg : 0 ≤ dist x y
:= begin
    unfold dist has_dist.dist Matrix.dist, simp,
end

lemma Matrix.eq_of_dist_eq_zero (x y : Vector n) : dist x y = 0 → x = y
:= begin
    intros h,
    have h': (dist x y) ^ 2 = 0, {
        rw h, simp,
    },
    have f1: inner (x - y) (x - y) = (0 : ℂ), {
        unfold dist has_dist.dist Matrix.dist Matrix.norm at h',
        rw pow_two at h',
        rw real.mul_self_sqrt at h', {
            rw <- re_inner_product_self,
            apply_mod_cast h',
        }, {
            simp,
        }
    },
    have f2: x - y = 0, {
        apply inner_product_self_zero f1,
    },
    have f2': x - y = y - y, {
        rw f2, simp,
    },
    apply sub_left_inj.mp f2',
end

lemma Matrix.dist_comm (x y : Vector n) : dist x y = dist y x
:= begin
    unfold dist has_dist.dist Matrix.dist,
    have f1: y - x = -(x - y), simp,
    rw f1,
    rw Matrix.norm_neg,
end

end dist


------------------------------------------------------------------------------
-- Pythagorean theorem

section pythagorean_theorem

variables {n : ℕ}
variables {x y z : Vector n}

theorem pythagorean_theorem : ⟪x,y⟫ = 0 → ∥x + y∥^2 = ∥x∥^2 + ∥y∥^2
:= begin
    intro h,

    have h': ⟪y,x⟫ = 0, {
        rw <- conj_inner_product,
        rw h, simp,
    },

    repeat { rw Matrix.norm_sq_eq_re_inner_product_self },
    rw inner_product_self_add,

    rw h,
    rw h',
    simp,
end

end pythagorean_theorem


------------------------------------------------------------------------------
-- cauchy_schwarz_inequality

section cauchy_schwarz_inequality

variables {n : ℕ}
variables {x y z : Vector n}

lemma matrix_add_app (i : fin n) : (x + y) i 0 = (x i 0) + (y i 0)
:= begin
    simp,
end
lemma matrix_sub_app (i : fin n) : (x - z) i 0 = (x i 0) - (z i 0)
:= begin
    simp,
end

variables {u v : Vector n}

lemma cauchy_schwarz_inequality_step1 : ∥u + v∥^2 = (∥u∥^2 + ⟪u,v⟫.re) + (⟪v,u⟫.re + ∥v∥^2)
:= begin
    rw Matrix.norm_sq_eq_re_inner_product_self,
    repeat { rw pow_two },

    unfold inner Matrix.inner_product,
    rw adjoint_add,
    rw matrix.add_mul,
    iterate 2 { rw matrix.mul_add },
    repeat { rw matrix_add_app },
    simp,

    unfold norm Matrix.norm, simp,
    unfold inner Matrix.inner_product,
end

lemma cauchy_schwarz_inequality_step2_1 : ⟪u,(-(⟪v,u⟫/⟪v,v⟫)) • v⟫ = (-|⟪u,v⟫|^2/⟪v,v⟫ : ℂ)
:= begin
    rw inner_product_smul_r,
    simp,
    ring,
    rw mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    rw inner_product_mul_eq_norm_sq,
    rw complex.norm_sq_eq_abs,
    norm_cast,
end

lemma cauchy_schwarz_inequality_step2_2 : ⟪(-(⟪v,u⟫/⟪v,v⟫)) • v, u⟫ = (-|⟪u,v⟫|^2/⟪v,v⟫ : ℂ)
:= begin
    rw inner_product_smul_l,
    simp,
    rw <- is_R_or_C.conj_to_complex,
    rw is_R_or_C.conj_div,
    rw conj_inner_product,
    simp,
    ring,
    simp,
    rw mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    rw inner_product_mul_eq_norm_sq,
    rw complex.norm_sq_eq_abs,
    norm_cast,
    repeat { rw <- is_R_or_C.abs_to_complex },
    rw abs_inner_product_comm,
end

lemma cauchy_schwarz_inequality_step2_3 : v ≠ 0 → ∥-(⟪v,u⟫/⟪v,v⟫) • v∥ ^ 2 = |⟪u,v⟫|^2/⟪v,v⟫.re
:= begin
    intro h,
    rw Matrix.norm_sq_eq_re_inner_product_self,
    rw inner_product_smul_l,
    rw inner_product_smul_r,
    rw <- smul_assoc,

    have f1: (-(⟪v,u⟫ / ⟪v,v⟫))† • (-(⟪v,u⟫ / ⟪v,v⟫))
           = (⟪v,u⟫ / ⟪v,v⟫).norm_sq, {
        simp,
    },
    rw f1, clear f1,
    rw complex.norm_sq_div,
    simp,
    norm_cast,
    rw complex.norm_sq_eq_abs,
    have f2: ⟪v,v⟫.norm_sq = ⟪v,v⟫.re * ⟪v,v⟫.re, {
        rw <- complex.norm_sq_eq_mul_abs, simp,
    },
    rw f2,
    ring,
    congr' 1, {
        rw mul_inv',
        rw <- mul_assoc,
        rw mul_inv_cancel, simp *,
        revert h,
        contrapose!,
        intro h,
        apply inner_product_self_zero,
        apply inner_product_self_re_inj; assumption,
    }, {
        repeat { rw <- is_R_or_C.abs_to_complex },
        rw abs_inner_product_comm,
    }
end

-- The equality part.
lemma cauchy_schwarz_inequality_part1 :
        v ≠ 0
        → ∥u - (⟪v,u⟫/⟪v,v⟫) • v∥ ^ 2 = ∥u∥^2 - (|⟪u,v⟫|^2 / ⟪v,v⟫ : ℂ).re
:= begin
    intros h,
    -- Step 1. Change the equation to (A + B) = (C + 0) form,
    have f1: u - (⟪v,u⟫/⟪v,v⟫) • v = u + (-(⟪v,u⟫/⟪v,v⟫)) • v, {
        simp, ring,
    },
    rw f1,
    rw cauchy_schwarz_inequality_step1,

    have f2: ∥u∥^2 - (|⟪u,v⟫|^2 / ⟪v,v⟫ : ℂ).re = (∥u∥^2 + (-|⟪u,v⟫|^2 / ⟪v,v⟫ : ℂ).re) + 0, {
        simp, ring,
    },
    rw f2,

    -- Step 2. Solve individual sub-equations of A = C and B = 0.
    congr' 1, {
        congr' 1,
        have f3: (⟪u,(-(⟪v,u⟫/⟪v,v⟫)) • v⟫).re = (-|⟪u,v⟫|^2/⟪v,v⟫ : ℂ).re, {
            rw cauchy_schwarz_inequality_step2_1,
        },
        apply f3,
    }, {
        rw cauchy_schwarz_inequality_step2_2,
        rw cauchy_schwarz_inequality_step2_3 h,
        rw complex.re_div_eq_div_re, {
            have f4: ∀ {r s : ℝ}, r = -s → r + s = 0, {intros r s h, rw h, simp,},
            apply f4,
            simp,
            norm_cast,
            ring,
        }, {
            rw pow_two, simp,
        }, {
            simp,
        }
    }
end

theorem cauchy_schwarz_inequality : |⟪u,v⟫|^2 ≤ ∥u∥^2 * ∥v∥^2
:= begin
    by_cases h: v = 0, {
        rw h,
        repeat { rw pow_two },
        simp,
    },

    -- case h: v ≠ 0,
    have f1: 0 ≤ ∥u∥^2 - (|⟪u,v⟫|^2 / ⟪v,v⟫ : ℂ).re, {
        rw <- cauchy_schwarz_inequality_part1; try {assumption},
        rw Matrix.norm_sq_eq_re_inner_product_self, simp,
    },
    have f2: (|⟪u,v⟫|^2 / ⟪v,v⟫ : ℂ).re ≤ ∥u∥^2, {
        have g1: ∀ (r s : ℝ), 0 ≤ r - s → s ≤ r, simp,
        apply g1,
        apply f1,
    },
    have f3: |⟪u,v⟫|^2 / ∥v∥^2 ≤ ∥u∥^2, {
        rw complex.re_div_eq_div_re at f2,
        rw Matrix.norm_sq_eq_re_inner_product_self,
        apply_mod_cast f2,
        rw pow_two; simp,
        simp,
    },
    clear f1 f2,
    apply (div_le_iff _).mp; try {assumption},
    rw Matrix.norm_sq_eq_re_inner_product_self,
    clear f3,

    let f4 := inner_product_self_re_nonneg v,
    have f5: ⟪v,v⟫.re ≠ 0, {
        revert h, contrapose!, intro h,
        apply inner_product_self_zero,
        apply inner_product_self_re_inj; assumption,
    },

    by_contradiction c,
    push_neg at c,
    apply f5, clear f5,
    linarith,
end

lemma cauchy_schwarz_inequality_alt : |⟪u,v⟫| ≤ ∥u∥ * ∥v∥
:= begin
    apply real.le_of_le_pow_two; try {solve1 {simp}}, {
        calc |⟪u,v⟫|^2 ≤ ∥u∥^2 * ∥v∥^2 : cauchy_schwarz_inequality
                   ... = (∥u∥ * ∥v∥)^2 : by ring,
    }, {
        apply mul_nonneg; simp,
    }
end

lemma inner_product_bound_of_unit (x y : Vector n) : x.unit → y.unit → |⟪x,y⟫| ≤ 1
:= begin
    intros xu yu,
    let f1 := @cauchy_schwarz_inequality_alt _ x y,
    rw norm_eq_one_of_unit xu at f1,
    rw norm_eq_one_of_unit yu at f1,
    calc |inner x y| ≤ 1 * 1 : f1
                  ...= 1 : by simp,
end

end cauchy_schwarz_inequality


------------------------------------------------------------------------------
section triangle_inequality
-- Wikipedia proof: depends on Cauchy-Schwarz inequality

variables {n : ℕ}
variables {x y z : Vector n}

lemma norm_sq_add_le_add_norm_sq : ∥x + y∥^2 ≤ (∥x∥ + ∥y∥)^2
:= begin
    -- Part 1. expand both sides of inequality
    rw Matrix.norm_sq_eq_re_inner_product_self,
    rw inner_product_self_add,
    repeat { rw complex.re_add_eq_add_re },

    repeat { rw pow_two },
    repeat { rw add_mul },
    repeat { rw mul_add },
    repeat { rw <- pow_two },
    repeat { rw Matrix.norm_sq_eq_re_inner_product_self },

    have f0: ⟪y,x⟫.re = ⟪x,y⟫.re, {
        rw re_inner_product_comm,
    },
    rw f0, clear f0,
    have f1: ⟪x,x⟫.re + ⟪x,y⟫.re + ⟪x,y⟫.re + ⟪y,y⟫.re = (⟪x,x⟫.re + ⟪y,y⟫.re) + (2 * ⟪x,y⟫.re), {
        ring,
    },
    rw f1, clear f1,
    have f2: ⟪x,x⟫.re + ∥x∥ * ∥y∥ + (∥y∥ * ∥x∥ + ⟪y,y⟫.re) = (⟪x,x⟫.re + ⟪y,y⟫.re) + 2 * ∥x∥ * ∥y∥, {
        ring,
    },
    rw f2, clear f2,

    -- Part 2. simplify inequality by canceling out identical terms
    simp,
    rw mul_assoc,

    have f3: ⟪x,y⟫.re ≤ (∥x∥ * ∥y∥) → 2 * ⟪x,y⟫.re ≤ 2 * (∥x∥ * ∥y∥), {
        intros h, linarith,
    },
    apply f3, clear f3,

    -- Part 3. solve the main inequality using Cauchy-Schwarz_inequality
    have f1: ⟪x,y⟫.re ≤ |⟪x,y⟫.re|, {
        simp, apply le_abs_self,
    },
    have f2: |⟪x,y⟫.re| ≤ |⟪x,y⟫|, {
        simp, apply complex.abs_re_le_abs,
    },
    calc ⟪x,y⟫.re ≤ |⟪x,y⟫.re| : f1
              ... ≤ |⟪x,y⟫| : f2
              ... ≤ ∥x∥ * ∥y∥ : cauchy_schwarz_inequality_alt,
end

lemma triangle_inequality : ∥x + y∥ ≤ ∥x∥ + ∥y∥
:= begin
    apply real.le_of_le_pow_two; try {solve1 {simp}}, {
        apply norm_sq_add_le_add_norm_sq,
    }, {
        apply add_nonneg; simp,
    }
end

end triangle_inequality


------------------------------------------------------------------------------
-- normed_group

section normed_group

variables {n : ℕ}
variables {x y z : Vector n}

lemma Matrix.dist_triangle : dist x z ≤ dist x y + dist y z
:= begin
    unfold dist Matrix.dist,
    have f1: x - z = (x - y) + (y - z), by abel,
    rw f1, clear f1,
    apply triangle_inequality,
end

noncomputable
instance : metric_space (Vector n) := {
    dist               := Matrix.dist,
    dist_self          := Matrix.dist_self,
    eq_of_dist_eq_zero := Matrix.eq_of_dist_eq_zero,
    dist_comm          := Matrix.dist_comm,
    dist_triangle      := by {apply Matrix.dist_triangle},
}

noncomputable
instance : normed_group (Vector n) := ⟨ Matrix.dist_eq ⟩

end normed_group


------------------------------------------------------------------------------
-- inner_product_space

section inner_product_space

variables {n : ℕ}
variables {x : Vector n}

noncomputable
instance : normed_space ℂ (Vector n) := {
    norm_smul_le := by {intros, rw Matrix.norm_smul,}
}

noncomputable
instance : inner_product_space ℂ (Vector n) := {
    norm_sq_eq_inner := by {intros, rw Matrix.norm_sq_eq_re_inner_product_self, simp,},
    conj_sym := by {intros, rw <- conj_inner_product, simp},
    nonneg_im := by {intros x, rw <- inner_product_self_im_zero x, simp},
    add_left := by {apply inner_product_add_left},
    smul_left := by {apply inner_product_smul_l},
}

end inner_product_space
