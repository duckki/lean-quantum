import data.matrix.basic
import analysis.normed_space.inner_product
import algebra.big_operators.default

open_locale big_operators
open is_R_or_C

------------------------------------------------------------------------------
-- ℝ lemmas

lemma real.le_of_le_pow_two {a b : ℝ} : a^2 ≤ b^2 → 0 ≤ a → 0 ≤ b → a ≤ b
:= begin
    intros h an bn,
    rw <- real.sqrt_mul_self an,
    rw <- real.sqrt_mul_self bn,
    iterate 2 { rw pow_two at h },
    apply real.sqrt_le_sqrt; assumption,
end


------------------------------------------------------------------------------
-- Begining of the namespace `matrix`

namespace matrix

-- We could use `has_star.star`, but `inner_product_space` expects `is_R_or_C` anyways.
local notation x `†`:90 := is_R_or_C.conj x
local notation |x| := is_R_or_C.abs x


------------------------------------------------------------------------------
-- matrix.conj for vectors

section conjugate

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type}

/--
Conjugate of a vector.
-/
def conj (v : m → 𝕜) : m → 𝕜 := λ i : m, (v i)†

end conjugate


------------------------------------------------------------------------------
-- matrix.conj lemmas

section conj_lemmas

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type}
variables {x y : m → 𝕜}

variable {s : 𝕜}

@[simp]
lemma conj_zero : conj 0 = (0 : m → 𝕜)
:= begin
    unfold conj,
    ext1 i, simp,
end

lemma conj_smul : conj (s • x) = s† • conj x
:= begin
    unfold conj,
    ext1 i,
    iterate 2 { rw pi.smul_apply }, simp,
end

lemma conj_add : conj (x + y) = conj x + conj y
:= begin
    unfold conj,
    ext1 i,
    iterate 2 { rw pi.add_apply }, simp,
end

lemma conj_neg : conj (-x) = - conj x
:= begin
    unfold conj,
    ext1 i,
    simp,
end

end conj_lemmas


------------------------------------------------------------------------------
-- matrix.inner_product for vectors

section inner_product

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]

/--
Inner product of vectors.
Following analysis.normed_space.inner_product's convention that
inner products are conjugate linear in the first argument and linear
in the second.
-/
def inner_product (x y : m → 𝕜) : 𝕜 := dot_product (conj x) y

instance : has_inner 𝕜 (m → 𝕜) := ⟨inner_product⟩

end inner_product

-- `⟪x, y⟫` : inner product notation.
-- `⟨ , ⟩` is already taken in Lean. So, use  `⟪ , ⟫`, instead.
-- Also, it's consistent with analysis.normed_space.inner_product's other notations.
local notation `⟪` X `,` Y `⟫` := inner_product X Y


------------------------------------------------------------------------------
-- matrix.inner_product lemmas

section inner_product_lemmas

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {x y z : m → 𝕜}

lemma inner_product_self_eq_sum_conj_mul : ⟪x, x⟫ = ∑ i, ((x i)†) * x i := by refl

lemma inner_product_self_eq_sum_norm_sq : ⟪x, x⟫ = ∑ i, norm_sq (x i)
:= begin
    rw inner_product_self_eq_sum_conj_mul,
    congr, apply funext, intro i,
    rw conj_mul_eq_norm_sq_left,
end

@[simp]
lemma inner_product_self_im_zero : im ⟪x, x⟫ = 0
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    rw <- finset.univ.sum_hom im,
    apply finset.sum_eq_zero, intros i ip, simp,
    split, simp,
end

@[simp]
lemma inner_product_self_re_eq_self : (re ⟪x,x⟫ : 𝕜) = ⟪x,x⟫
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    rw <- finset.univ.sum_hom re, {
        simp,
    }, {
        split, simp,
    }
end

-- Positive semi-definite or nonnegative-definite
@[simp]
lemma inner_product_self_re_nonneg (x : m → 𝕜) : 0 ≤ re ⟪x, x⟫
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    rw <- finset.univ.sum_hom re, {
        apply finset.sum_nonneg,
        intros i ip, simp,
        apply norm_sq_nonneg,
    }, {
        split, simp,
    }
end

-- Point-separating or non-degenerate
lemma inner_product_self_zero : ⟪x, x⟫ = 0 → x = 0
:= begin
    rw inner_product_self_eq_sum_norm_sq,
    intros h,

    have h': ∑ (i : m), norm_sq (x i) = 0, {
        apply_mod_cast h,
    },
    clear h,

    have f1: ∀ i, norm_sq (x i) = 0, {
        intro i,
        apply (finset.sum_eq_zero_iff_of_nonneg _).mp h'; simp,
        intros, apply norm_sq_nonneg,
    },

    have f2: ∀ i, x i = 0, {
        intros i,
        apply norm_sq_eq_zero.mp; apply f1,
    },

    ext i,
    apply f2,
end

lemma inner_product_self_add : ⟪x+y , x+y⟫ = ⟪x,x⟫ + ⟪x,y⟫ + ⟪y,x⟫ + ⟪y,y⟫
:= begin
    unfold inner_product,
    rw conj_add,
    repeat { rw add_dot_product },
    repeat { rw dot_product_add },
    ring,
end

@[simp]
lemma inner_product_self_neg : ⟪-x, -x⟫ = ⟪x, x⟫
:= begin
    unfold inner_product,
    rw conj_neg, simp,
end

variable {s : 𝕜}

lemma inner_product_smul_l {s : 𝕜} : ⟪s • x, y⟫ = (s†) * ⟪x, y⟫
:= begin
    unfold inner_product,
    rw conj_smul,
    rw smul_dot_product,
end

lemma inner_product_smul_r {s : 𝕜} : ⟪x, s • y⟫ = s * ⟪x, y⟫
:= begin
    unfold inner_product,
    rw dot_product_smul,
end

lemma inner_product_add_left : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
:= begin
    unfold inner_product,
    rw conj_add,
    rw add_dot_product,
end

lemma inner_product_add_right : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
:= begin
    unfold inner_product,
    rw dot_product_add,
end

@[simp]
lemma inner_product_zero_r : ⟪x,(0 : m → 𝕜)⟫ = 0
:= by { unfold inner inner_product, simp, }

@[simp]
lemma inner_product_zero_l : ⟪(0 : m → 𝕜),x⟫ = 0
:= by { unfold inner inner_product, simp, }

@[simp]
lemma conj_inner_product : ⟪y, x⟫† = ⟪x, y⟫
:= begin
    unfold matrix.inner_product,
    unfold matrix.dot_product,
    rw <- finset.univ.sum_hom is_R_or_C.conj, {
        congr' 1, apply funext, intro i,
        unfold conj,
        simp, ring,
    }, {
        split; simp,
    }
end

lemma inner_product_mul_eq_norm_sq : ⟪x, y⟫ * ⟪y, x⟫ = norm_sq ⟪y, x⟫
:= begin
    rw <- conj_inner_product,
    rw conj_mul_eq_norm_sq_left,
end

lemma abs_inner_product_comm : |⟪x, y⟫| = |⟪y, x⟫|
:= begin
    rw <- conj_inner_product,
    rw is_R_or_C.abs_conj,
end

lemma re_inner_product_comm : re ⟪x, y⟫ = re ⟪y, x⟫
:= begin
    rw <- conj_inner_product,
    apply conj_re,
end

end inner_product_lemmas


------------------------------------------------------------------------------
-- matrix.norm for a vector

section norm

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]

/--
Norm of a vector
-/
noncomputable
def norm (x : m → 𝕜) : ℝ := (re ⟪x, x⟫).sqrt

noncomputable
instance : has_norm (m → 𝕜) := ⟨norm⟩

-- Use the standard norm notation of `∥x∥`

end norm


------------------------------------------------------------------------------
-- matrix.norm lemmas

section norm_lemmas

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {x : m → 𝕜}

lemma norm_smul (s : 𝕜) : norm (s • x) = ∥s∥ * norm x
:= begin
    have f1: ∥s∥ = real.sqrt (norm_sq s), {
        rw norm_sq_eq_abs,
        rw pow_two,
        rw real.sqrt_mul_self, {
            apply norm_eq_abs,
        }, {
            apply is_R_or_C.abs_nonneg,
        }
    },
    rw f1, clear f1,

    unfold norm,
    rw inner_product_smul_l,
    rw inner_product_smul_r,
    rw <- mul_assoc,
    rw conj_mul_eq_norm_sq_left,
    simp,
end

@[simp]
lemma norm_zero : norm (0 : m → 𝕜) = 0
:= begin
    unfold norm, simp [inner_product_self_eq_sum_norm_sq],
end

@[simp]
lemma norm_nonneg : 0 ≤ norm x
:= begin
    unfold norm, apply real.sqrt_nonneg,
end

@[simp]
lemma norm_neg : norm (-x) = norm x
:= begin
    unfold norm, simp,
end

end norm_lemmas


-- has_norm.norm lemmas for proof automation
section has_norm_lemmas

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {x : m → 𝕜}

lemma has_norm_sq_eq_re_inner_product_self : ∥x∥^2 = re ⟪x, x⟫
:= begin
    unfold has_norm.norm norm,
    rw pow_two,
    rw real.mul_self_sqrt, simp,
end

@[simp]
lemma has_norm_zero : ∥(0 : m → 𝕜)∥ = 0
:= begin
    unfold has_norm.norm norm, simp,
end

@[simp]
lemma has_norm_nonneg : 0 ≤ ∥x∥
:= begin
    unfold has_norm.norm norm,
    apply real.sqrt_nonneg,
end

end has_norm_lemmas


------------------------------------------------------------------------------
-- cauchy_schwarz_inequality

section cauchy_schwarz_inequality

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {u v : m → 𝕜}

lemma cauchy_schwarz_inequality_step1 : ∥u + v∥^2 = (∥u∥^2 + re ⟪u,v⟫) + (re ⟪v,u⟫ + ∥v∥^2)
:= begin
    iterate 3 { rw has_norm_sq_eq_re_inner_product_self },
    repeat { rw pow_two },

    unfold inner inner_product,
    rw conj_add,
    rw dot_product_add,
    iterate 2 { rw add_dot_product },
    have vector_add_apply: ∀ {i : m} {x y : m → 𝕜}, (x + y) i = (x i) + (y i), by {intros, simp},
    repeat { rw vector_add_apply },
    simp,
    ring,
end

lemma cauchy_schwarz_inequality_step2_1 : ⟪u,(-(⟪v,u⟫/⟪v,v⟫)) • v⟫ = -|⟪u,v⟫|^2/⟪v,v⟫
:= begin
    rw inner_product_smul_r,
    simp,
    ring,
    rw mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    rw inner_product_mul_eq_norm_sq,
    rw norm_sq_eq_abs, simp,
end

lemma cauchy_schwarz_inequality_step2_2 : ⟪(-(⟪v,u⟫/⟪v,v⟫)) • v, u⟫ = -|⟪u,v⟫|^2/⟪v,v⟫
:= begin
    rw inner_product_smul_l,
    simp,
    rw is_R_or_C.conj_div,
    rw conj_inner_product,
    simp,
    ring,
    simp,
    rw mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    rw inner_product_mul_eq_norm_sq,
    rw norm_sq_eq_abs,
    norm_cast,
    repeat { rw <- is_R_or_C.abs_to_complex },
    rw abs_inner_product_comm,
end

lemma cauchy_schwarz_inequality_step2_3 : v ≠ 0 → ∥-(⟪v,u⟫/⟪v,v⟫) • v∥ ^ 2 = |⟪u,v⟫|^2/(re ⟪v,v⟫)
:= begin
    intro h,
    rw has_norm_sq_eq_re_inner_product_self,
    rw inner_product_smul_l,
    rw inner_product_smul_r,
    rw <- mul_assoc,

    have f1: (-(⟪v,u⟫ / ⟪v,v⟫))† * (-(⟪v,u⟫ / ⟪v,v⟫))
           = norm_sq (⟪v,u⟫ / ⟪v,v⟫), {
        simp [conj_mul_eq_norm_sq_left],
    },
    rw f1, clear f1,
    rw norm_sq_div,
    simp,
    norm_cast,
    rw norm_sq_eq_abs,

    have f2: norm_sq ⟪v,v⟫ = re ⟪v,v⟫ * re ⟪v,v⟫, {
        unfold norm_sq, simp,
    },
    rw f2, clear f2,
    ring,
    congr' 1, {
        rw mul_inv',
        rw <- mul_assoc,
        rw mul_inv_cancel, simp *,
        revert h,
        contrapose!,
        intro h,
        apply inner_product_self_zero,
        have f3: (re ⟪v,v⟫ : 𝕜) = 0, {
            rw h, simp,
        },
        simp at f3, apply f3,
    }, {
        repeat { rw <- is_R_or_C.abs_to_complex },
        rw abs_inner_product_comm,
    }
end

-- The equality part.
lemma cauchy_schwarz_inequality_part1 :
        v ≠ 0
        → ∥u - (⟪v,u⟫/⟪v,v⟫) • v∥ ^ 2 = ∥u∥^2 - re (|⟪u,v⟫|^2 / ⟪v,v⟫ : 𝕜)
:= begin
    intros h,
    -- Step 1. Change the equation to (A + B) = (C + 0) form,
    have f1: u - (⟪v,u⟫/⟪v,v⟫) • v = u + (-(⟪v,u⟫/⟪v,v⟫)) • v, {
        simp, ring,
    },
    rw f1,
    rw cauchy_schwarz_inequality_step1,

    have f2: ∥u∥^2 - re (|⟪u,v⟫|^2 / ⟪v,v⟫ : 𝕜) = (∥u∥^2 + re (-|⟪u,v⟫|^2 / ⟪v,v⟫ : 𝕜)) + 0, {
        rw neg_div, simp, ring,
    },
    rw f2,

    -- Step 2. Solve individual sub-equations of A = C and B = 0.
    congr' 1, {
        congr' 1,
        have f3: re (⟪u,(-(⟪v,u⟫/⟪v,v⟫)) • v⟫) = re (-|⟪u,v⟫|^2/⟪v,v⟫ : 𝕜), {
            rw cauchy_schwarz_inequality_step2_1,
        },
        apply f3,
    }, {
        rw cauchy_schwarz_inequality_step2_2,
        rw cauchy_schwarz_inequality_step2_3 h,
        have f4: ∀ {r s : ℝ}, r = -s → r + s = 0, {intros r s h, rw h, simp,},
        apply f4,
        have f5: ∀ {r s : ℝ}, -(r/s) = re (-r / s : 𝕜), {
            intros, norm_cast, ring,
        },
        rw f5, clear f5, simp,
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
    have f1: 0 ≤ ∥u∥^2 - re (|⟪u,v⟫|^2 / ⟪v,v⟫ : 𝕜), {
        rw <- cauchy_schwarz_inequality_part1; try {assumption},
        rw has_norm_sq_eq_re_inner_product_self, simp,
    },
    have f2: re (|⟪u,v⟫|^2 / ⟪v,v⟫ : 𝕜) ≤ ∥u∥^2, {
        have g1: ∀ (r s : ℝ), 0 ≤ r - s → s ≤ r, simp,
        apply g1,
        apply f1,
    },
    have f3: |⟪u,v⟫|^2 / ∥v∥^2 ≤ ∥u∥^2, {
        rw has_norm_sq_eq_re_inner_product_self,
        have f3': ∀ {r s : ℝ}, r/s = re (r / s : 𝕜), {
            intros, norm_cast,
        },
        rw f3', simp,
        apply_mod_cast f2,
    },
    clear f1 f2,
    apply (div_le_iff _).mp; try {assumption},
    clear f3,
    rw has_norm_sq_eq_re_inner_product_self,

    let f4 := inner_product_self_re_nonneg v,
    have f5: re ⟪v,v⟫ ≠ 0, {
        revert h, contrapose!, intro h,
        apply inner_product_self_zero,
        have f5': (re ⟪v,v⟫ : 𝕜) = 0, {
            rw h, simp,
        },
        simp at f5', apply f5',
    },

    by_contradiction c,
    push_neg at c,
    apply f5, clear f5,
    linarith,
end

lemma cauchy_schwarz_inequality_alt : |⟪u,v⟫| ≤ ∥u∥ * ∥v∥
:= begin
    apply real.le_of_le_pow_two, {
        calc |⟪u,v⟫|^2 ≤ ∥u∥^2 * ∥v∥^2 : cauchy_schwarz_inequality
                   ... = (∥u∥ * ∥v∥)^2 : by ring,
    }, {
        apply is_R_or_C.abs_nonneg,
    }, {
        apply mul_nonneg; simp,
    }
end

end cauchy_schwarz_inequality


------------------------------------------------------------------------------
section triangle_inequality
-- Wikipedia proof: depends on Cauchy-Schwarz inequality

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {x y : m → 𝕜}

lemma norm_sq_add_le_add_norm_sq : ∥x + y∥^2 ≤ (∥x∥ + ∥y∥)^2
:= begin
    -- Part 1. expand both sides of inequality
    rw has_norm_sq_eq_re_inner_product_self,
    rw inner_product_self_add,
    simp,

    repeat { rw pow_two },
    repeat { rw add_mul },
    repeat { rw mul_add },
    repeat { rw <- pow_two },
    repeat { rw has_norm_sq_eq_re_inner_product_self },

    have f0: re ⟪y,x⟫ = re ⟪x,y⟫, {
        rw re_inner_product_comm,
    },
    rw f0, clear f0,
    have f1: re ⟪x,x⟫ + re ⟪x,y⟫ + re ⟪x,y⟫ + re ⟪y,y⟫ = (re ⟪x,x⟫ + re ⟪y,y⟫) + (2 * re ⟪x,y⟫), {
        ring,
    },
    rw f1, clear f1,
    have f2: re ⟪x,x⟫ + ∥x∥ * ∥y∥ + (∥y∥ * ∥x∥ + re ⟪y,y⟫) = (re ⟪x,x⟫ + re ⟪y,y⟫) + 2 * ∥x∥ * ∥y∥, {
        ring,
    },
    rw f2, clear f2,

    -- Part 2. simplify inequality by canceling out identical terms
    simp,
    rw mul_assoc,

    have f3: re ⟪x,y⟫ ≤ (∥x∥ * ∥y∥) → 2 * re ⟪x,y⟫ ≤ 2 * (∥x∥ * ∥y∥), {
        intros h, linarith,
    },
    apply f3, clear f3,

    -- Part 3. solve the main inequality using Cauchy-Schwarz_inequality
    have f1: re ⟪x,y⟫ ≤ |re ⟪x,y⟫|, {
        simp, apply le_abs_self,
    },
    have f2: |re ⟪x,y⟫| ≤ |⟪x,y⟫|, {
        simp, apply abs_re_le_abs,
    },
    calc re ⟪x,y⟫ ≤ |re ⟪x,y⟫| : f1
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
-- dist

section dist

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]

/--
Distance between two vectors
-/
noncomputable
def dist (x y : m → 𝕜) := norm (x - y)

noncomputable
instance : has_dist (m → 𝕜) := ⟨dist⟩

end dist


------------------------------------------------------------------------------
-- dist lemmas

section dist_lemmas

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {x y z : m → 𝕜}

lemma dist_self : dist x x = 0
:= begin
    unfold dist, simp,
end

lemma eq_of_dist_eq_zero : dist x y = 0 → x = y
:= begin
    intros h,
    have h': (dist x y) ^ 2 = 0, {
        rw h, simp,
    },
    have f1: ⟪x - y, x - y⟫ = (0 : 𝕜), {
        unfold has_dist.dist dist norm at h',
        rw pow_two at h',
        rw real.mul_self_sqrt at h', {
            rw <- inner_product_self_re_eq_self,
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

lemma dist_comm : dist x y = dist y x
:= begin
    unfold has_dist.dist dist,
    have f1: y - x = -(x - y), simp,
    rw f1,
    rw norm_neg,
end

lemma dist_triangle : dist x z ≤ dist x y + dist y z
:= begin
    unfold dist,
    have f1: x - z = (x - y) + (y - z), by abel,
    rw f1, clear f1,
    apply triangle_inequality,
end

end dist_lemmas


------------------------------------------------------------------------------
-- normed_group

section normed_group

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {x y z : m → 𝕜}

noncomputable
instance : metric_space (m → 𝕜) := {
    dist               := dist,
    dist_self          := by {apply dist_self},
    eq_of_dist_eq_zero := by {apply eq_of_dist_eq_zero},
    dist_comm          := by {apply dist_comm},
    dist_triangle      := by {apply dist_triangle},
}

lemma dist_eq (x y : m → 𝕜) : dist x y = ∥x - y∥ := by refl

noncomputable
instance : normed_group (m → 𝕜) := ⟨ dist_eq ⟩

end normed_group


------------------------------------------------------------------------------
-- inner_product_space

section inner_product_space

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {m : Type} [fintype m]
variables {x : m → 𝕜}

noncomputable
instance : normed_space 𝕜 (m → 𝕜) := {
    norm_smul_le := by {
        intros,
        unfold has_norm.norm,
        rw norm_smul,
    }
}

noncomputable
instance : inner_product_space 𝕜 (m → 𝕜) := {
    norm_sq_eq_inner := by {unfold inner, intros, rw has_norm_sq_eq_re_inner_product_self},
    conj_sym := by {unfold inner, intros, rw <- conj_inner_product, simp},
    nonneg_im := by {unfold inner, intros x, simp},
    add_left := by {unfold inner, apply inner_product_add_left},
    smul_left := by {unfold inner, apply inner_product_smul_l},
}

end inner_product_space


------------------------------------------------------------------------------
-- End of namespace `matrix`

end matrix
