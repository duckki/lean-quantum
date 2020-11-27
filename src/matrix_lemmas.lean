import matrix
import common_lemmas
import linear_algebra.nonsingular_inverse

open_locale big_operators
open complex
open matrix
open Matrix

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

lemma real.lt_of_lt_pow_two {a b : ℝ} : a^2 < b^2 → 0 ≤ a → 0 ≤ b → a < b
:= begin
    intros h an bn,
    rw <- real.sqrt_mul_self an,
    rw <- real.sqrt_mul_self bn,
    iterate 2 { rw pow_two at h },
    apply (real.sqrt_lt _ _).mpr, assumption,
    rw <- pow_two; apply pow_two_nonneg,
    rw <- pow_two; apply pow_two_nonneg,
end

lemma real.add_squares_le_square_add (x y : ℝ): 0 ≤ x → 0 ≤ y → x^2 + y^2 ≤ (x + y)^2
:= begin
    intros xn yn,
    repeat { rw pow_two },
    repeat { rw mul_add },
    repeat { rw add_mul },
    have f1: x * x + y * x + (x * y + y * y) = (x * x + y * y) + (x * y + y * x), {
        ring,
    },
    rw f1,
    simp [add_nonneg, mul_nonneg, *],
end


------------------------------------------------------------------------------
-- (pure) ℂ lemmas

@[simp]
lemma complex.abs_nonneg' (c : ℂ) : 0 ≤ c.abs := by apply complex.abs_nonneg

@[simp]
lemma complex.norm_sq_nonneg' (c : ℂ) : 0 ≤ complex.norm_sq c := by apply complex.norm_sq_nonneg

@[simp]
lemma complex.conj_mul (c : ℂ) : c.conj * c = c.norm_sq
:= begin
    rw mul_comm,
    apply complex.mul_conj,
end

@[simp]
lemma complex.conj_mul' (c : ℂ) : c * c.conj = c.norm_sq
:= begin
    apply complex.mul_conj,
end

lemma complex.re_div_eq_div_re (a b : ℂ) : a.im = 0 → b.im = 0 → (a / b).re = a.re / b.re
:= begin
    intros ap bp,
    have f1: a = a.re, {
        cases a,
        cases b,
        cases ap,
        cases bp,
        simp at *,
        refl,
    },
    have f2: b = b.re, {
        cases a,
        cases b,
        cases ap,
        cases bp,
        simp at *,
        refl,
    },
    have f3: (a / b) = (a.re / b.re), {
        rw f1,
        rw f2,
        simp,
    },
    rw f3,
    norm_cast,
end

lemma complex.re_add_eq_add_re (a b : ℂ) : (a + b).re = a.re + b.re
:= begin
    exact rfl,
end


----------------------------------------------------------------------------------------
-- ℂ + is_R_or_C

lemma complex.mul_conj_abs_square (c : ℂ) : (c†) * c = |c| ^ 2
:= begin
    simp,
    apply_mod_cast norm_sq_eq_abs,
end

lemma complex.abs_of_real' (x : ℝ) : |x| = |(x : ℂ)|
:= begin
    refl,
end

lemma complex.re_conj_eq_re (c : ℂ): (c†).re = c.re
:= begin
    refl,
end

lemma complex.conj_sum_dist {n} (f : fin n → ℂ)
        : (∑ k, (f k)†) = (∑ k, (f k))†
:= begin
    exact finset.univ.sum_hom complex.conj,
end

@[simp]
lemma complex.norm_sq_eq_mul_abs (c : ℂ) : |c| * |c| = c.norm_sq
:= begin
    rw complex.norm_sq_eq_abs,
    rw pow_two, simp,
end


----------------------------------------------------------------------------------------
-- matrix type-cast helpers

section matrix_cast

variables {α : Type} [semiring α]
variables {m n : Type} [fintype m] [fintype n]
variables {m' n' : Type} [fintype m'] [fintype n']

variables (s : α) (M : matrix m n α) (N : matrix m n α)

lemma matrix_congr (h1: m = m') (h2: n = n') : matrix m n α = matrix m' n' α
:= begin
    congr; assumption,
end

lemma push_cast_matrix_smul (h1: m = m') (h2: n = n')
        : cast (matrix_congr h1 h2) (s • M) = s • (cast (matrix_congr h1 h2) M)
:= begin
    apply cast_eq_of_heq,
    tactic.unfreeze_local_instances,
    cases h1,
    cases h2,
    congr' 1; try {assumption},
end

lemma push_cast_matrix_add (h1: m = m') (h2: n = n')
        : cast (matrix_congr h1 h2) (M + N) = (cast (matrix_congr h1 h2) M) + (cast (matrix_congr h1 h2) N)
:= begin
    apply cast_eq_of_heq,
    tactic.unfreeze_local_instances,
    cases h1,
    cases h2,
    congr; try {assumption},
end

end matrix_cast

section matrix_cast_apply

variables {α : Type}
variables {m n m' n': Type} [fintype m] [fintype n] [fintype m'] [fintype n']
variables (A : matrix m n α) (B : matrix m' n' α)

lemma A_eq (m_eq: m = m') (n_eq: n = n') : matrix m n α = matrix m' n' α
:= begin
    congr; assumption,
end

-- for easier pattern matching with matrix
lemma matrix_cast_apply (m_eq: m = m') (n_eq: n = n') (i' : m') (j' : n')
    : (cast (A_eq m_eq n_eq) A) i' j' = A (cast m_eq.symm i') (cast n_eq.symm j')
:= begin
    apply cast_apply2,
end

end matrix_cast_apply


----------------------------------------------------------------------------------------
-- Matrix lemmas

section matrix

variables {m n : ℕ}
variables {A : Matrix m n}
variables {s : Vector n}

@[simp]
lemma Matrix_zero_neq_one {n} : 0 ≠ (I (n+1))
:= begin
    intro h,
    have c3: (1 : ℂ) = 0, {
        calc (1 : ℂ) = (I (n+1)) 0 0 : by simp
              ... = (0 : Square (n+1)) 0 0 : by {rw h}
              ... = 0 : by simp,
    },
    have c4: (1 : ℝ) = 0, {
        apply_mod_cast c3,
    },
    linarith,
end

lemma Matrix_nonzero_has_nonzero_val : A ≠ 0 → (∃ i j, A i j ≠ 0)
:= begin
    contrapose!, intros h,
    apply matrix.ext, intros i j,
    apply h,
end

lemma Vector_nonzero_has_nonzero_val : s ≠ 0 → (∃ i, s i 0 ≠ 0)
:= begin
    contrapose!, intros h,
    apply matrix.ext, intros i j,
    have j0 : j = 0, cases j, simp, cases j0, clear j0, simp,
    apply h,
end

-- Special case of 1 × 1 matrix.
lemma matrix_mul_cancel_left_square_one {n} {x : Vector n} {y z : Square 1} : x ⬝ y = x ⬝ z → x ≠ 0 → y = z
:= begin
    intros h xn,
    apply matrix.ext, intros i j,
    rw <- matrix.ext_iff at h,

    cases (Vector_nonzero_has_nonzero_val xn) with k kp,

    specialize h k j,

    iterate 2 {
        rw matrix.mul_apply at h,
        rw finset.sum_fin_eq_sum_range at h,
        rw finset.sum_range_one at h,
        rw dif_pos at h; try {solve1 {linarith}}, simp at h,
    },

    have i0 : i = 0, cases i; simp, cases i0; clear i0,
    have j0 : j = 0, cases j; simp, cases j0; clear j0,
    simp at *,

    cases h, {
        assumption,
    }, {
        exfalso,
        apply kp; assumption,
    }
end

-- Special case of 1 × 1 matrix.
lemma matrix_mul_square_one {x y : Square 1} {i j : fin 1}: (x ⬝ y) i j = x i j * y i j
:= begin
    unfold matrix.mul matrix.dot_product,
    have i0 : i = 0, cases i; simp, cases i0; clear i0,
    have j0 : j = 0, cases j; simp, cases j0; clear j0,
    rw finset.sum_fin_eq_sum_range,
    rw finset.sum_range_one,
    rw dif_pos; simp,
end

-- Special case of 1 × 1 matrix.
lemma matrix_mul_comm_square_one {x y : Square 1} : x ⬝ y = y ⬝ x
:= begin
    apply matrix.ext, intros i j,
    iterate 2 { rw matrix_mul_square_one },
    ring,
end

-- Special case of 1 × 1 matrix.
@[simp]
lemma id_one_apply {x y : fin 1} : (I 1) x y = 1
:= begin
    have xp: x = 0, by simp,
    have yp: y = 0, by simp,
    cases xp,
    cases yp,
    simp,
end

end matrix


----------------------------------------------------------------------------------------
-- adjoint lemmas

@[simp]
theorem adjoint_zero {m n} : (0 : Matrix m n)† = 0
:= begin
    apply matrix.ext, intros i j,
    unfold adjoint, simp,
end

@[simp]
theorem adjoint_one {n} : (1 : Matrix n n)† = 1
:= begin
    apply matrix.ext,
    intros i j,
    unfold adjoint,
    by_cases i = j, {
        simp [h],
    }, {
        rw matrix.one_apply_ne h,
        have h' : ¬ j = i, {
            cc,
        },
        rw matrix.one_apply_ne h',
        simp,
    }
end

section adjoint

variables {m n : ℕ}
variables (x y : Matrix m n)

@[simp]
theorem adjoint_involutive : x†† = x
:= begin
    apply matrix.ext,
    intros i j,
    unfold adjoint,
    simp,
end

theorem adjoint_inj : (x†) = (y†) → x = y
:= begin
    intros h,
    apply matrix.ext, intros i j,
    rw <- matrix.ext_iff at h,
    specialize h j i,
    unfold adjoint at h,
    apply complex.conj_inj.mp h,
end

lemma adjoint_add : ((x + y)†) = (x†) + (y†)
:= begin
    apply matrix.ext, intros i j, simp,
    unfold adjoint, simp,
end

lemma adjoint_neg (x : Matrix m n): (-x)† = -(x†)
:= begin
    apply matrix.ext, intros i j,
    simp, unfold adjoint, simp,
end

lemma adjoint_smul (s : ℂ) : (s • x)† = (s†) • (x†)
:= begin
    apply matrix.ext, intros i j,
    unfold has_scalar.smul,
    unfold adjoint,
    simp,
end

lemma adjoint_apply (x : Matrix m n) (i : fin n) (j : fin m) : (x†) i j = ((x j i)†)
:= begin
    unfold adjoint,
end


end adjoint


---------------------------------------------------------------------------------------------
-- Adjoint + mul lemmas

section adjoint_mul

variables {m n o : ℕ}
variable (A : Matrix m n)
variable (B : Matrix n o)

lemma conj_mul_eq_dot_product (i : fin m) (j : fin o)
        : ((A ⬝ B) i j)† = dot_product (λ k, (B k j)†)
                                       (λ k, (A i k)†)
:= begin
    unfold matrix.dot_product,
    unfold matrix.mul,
    unfold matrix.dot_product,
    rw <- complex.conj_sum_dist, {
        congr,
        refine funext _,
        intro k,
        simp,
        ring,
    },
end

theorem adjoint_mul : (A ⬝ B)† = (B†) ⬝ (A†)
:= begin
    apply matrix.ext,
    intros j i,
    apply conj_mul_eq_dot_product,
end

end adjoint_mul


----------------------------------------------------------------------------------------
-- Vector + adjoint lemmas

section vector_adjoint

variables {n : ℕ} (s : Vector n)

lemma dot_adjoint_eq_sum_mul_conj
            : dot_product (s† 0) (λ j, s j 0)
            = ∑ j, ((s j 0)†) * (s j 0)
:= begin
    congr,
end

lemma dot_adjoint_eq_sum_squre
            : dot_product (s† 0) (λ j, s j 0)
            = ∑ j, |s j 0| ^ 2
:= begin
    rw dot_adjoint_eq_sum_mul_conj,
    congr,
    apply funext,
    intros x,
    apply complex.mul_conj_abs_square,
end

example : (((s†) ⬝ s) 0 0) = ((∑ i, |s i 0| ^ 2) : ℂ)
:= begin
    apply dot_adjoint_eq_sum_squre,
end

@[simp]
lemma sum_square_one_if_mul_adjoint_one : ((s†) ⬝ s) = 1 → (∑ i, |s i 0| ^ 2) = 1
:= begin
    intros h,
    unfold matrix.mul at h,
    rw <- matrix.ext_iff at h,
    specialize h 0 0,
    rw dot_adjoint_eq_sum_squre at h,
    simp at h,
    apply_mod_cast h,
end

lemma mul_adjoint_one_if_sum_square_one : (∑ i, |s i 0| ^ 2) = 1 → ((s†) ⬝ s) = 1
:= begin
    intros h,
    apply matrix.ext,
    intros i j,
    have i_eq : i = 0, {
        cases i with i ip; simp,
    },
    have j_eq : j = 0, {
        cases i with i ip; simp,
    },
    cases i_eq,
    cases j_eq,
    simp,
    unfold matrix.mul,
    rw dot_adjoint_eq_sum_squre,
    apply_mod_cast h,
end

end vector_adjoint


----------------------------------------------------------------------------------------
-- unit lemmas

lemma unfold_unit {n} {s : Vector n} : s.unit -> (s†) ⬝ s = 1 := by {tautology}

lemma unit_nonzero {n : ℕ} {s : Vector n} : s.unit → s ≠ 0
:= begin
    contrapose!, intros h c,

    rw <- matrix.ext_iff at h, simp at h,

    unfold matrix.unit at c,
    rw <- matrix.ext_iff at c,
    specialize (c 0 0),
    unfold matrix.mul matrix.dot_product at c, simp at c,

    have h1: ∑ (i : fin n), s† 0 i * s i 0 = 0, {
        apply finset.sum_eq_zero, intros i ip,
        rw h, simp,
    },

    have c2: (0 : ℂ) = 1, {
        rw <- h1,
        rw <- c,
    },
    norm_num at c2,
end


----------------------------------------------------------------------------------------
-- std_basis lemmas

section std_basis

variables {m : Type*} [fintype m]
variables [decidable_eq m]

@[simp]
lemma std_basis_eq_zero {n : m} : ∀ {j i}, ¬ j = n → std_basis n j i = 0
:= begin
    intros j i h,
    unfold std_basis,
    exact if_neg h,
end

@[simp]
lemma std_basis_eq_one {n : m} : ∀ {j i}, j = n → std_basis n j i = 1
:= begin
    intros j i h,
    rw h,
    unfold std_basis,
    simp,
end

@[simp]
theorem std_basis_unit {n} {i : fin n} : (std_basis i).unit
:= begin
    apply mul_adjoint_one_if_sum_square_one,
    rw finset.sum_eq_single i, {
        simp,
    }, {
        intros b bp h,
        rw std_basis_eq_zero h; simp,
    }, {
        intro h,
        exfalso,
        apply h; simp,
    }
end

@[simp]
lemma std_basis_adjoint_apply {n} {s : fin n} : ∀ {i j}, ((std_basis s)†) i j = (std_basis s) j i
:= begin
    unfold Matrix.adjoint,
    intros i j,
    by_cases c : j = s, {
        rw std_basis_eq_one c, simp,
    }, {
        rw std_basis_eq_zero c, simp,
    }
end

@[simp]
lemma std_basis_inner_product {n} (i : fin n) : ((std_basis i)†) ⬝ (std_basis i) = 1
:= begin
    apply std_basis_unit,
end

lemma std_basis_inner_product_eq_zero {n} (i j : fin n) : ¬ i = j → ((std_basis i)†) ⬝ (std_basis j) = 0
:= begin
    intros h,

    apply matrix.ext, intros v w,
    unfold matrix.mul matrix.dot_product Matrix.adjoint,
    have v0 : v = 0, by simp,
    have w0 : w = 0, by simp,
    rw v0, rw w0, simp,

    rw finset.sum_eq_single i; simp [std_basis_eq_zero h],

    intros b h',
    left,
    rw std_basis_eq_zero h',
end

end std_basis


----------------------------------------------------------------------------------------
-- lemmas about matrix_std_basis from mathlib

section matrix_std_basis

variables {m n: Type*} [fintype m] [fintype n]
variables [decidable_eq m] [decidable_eq n]
variables {α : Type} [semiring α]

@[simp]
lemma std_basis_matrix_eq_given {i' : m} {j' : n} {v : α}
        : ∀ {i j}, i = i' ∧ j = j' → std_basis_matrix i' j' v i j = v
:= begin
    intros i j h,
    cases h with h1 h2,
    rw h1,
    rw h2,
    unfold std_basis_matrix,
    simp,
end

lemma std_basis_matrix_eq_zero {i' : m} {j' : n} {v : α}
        : ∀ {i j}, ¬ i = i' ∨ ¬ j = j' → std_basis_matrix i' j' v i j = 0
:= begin
    intros i j h,
    unfold std_basis_matrix,
    rwa if_neg,
    by_contradiction c,
    cases c with c1 c2,
    cases h, {
        apply h; assumption,
    }, {
        apply h; assumption,
    }
end

lemma std_basis_eq_std_basis_matrix {n : m}
        : std_basis n = matrix.std_basis_matrix n 0 1
:= begin
    apply matrix.ext,
    intros i j,
    have jp : j = 0, {
        cases j with j jp,
        simp,
    },
    cases jp,
    simp,
    by_cases i = n, {
        cases h,
        simp,
    }, {
        rw std_basis_eq_zero h,
        rw std_basis_matrix_eq_zero,
        left, assumption,
    }
end

end matrix_std_basis


----------------------------------------------------------------------------------------
-- state vector decomposition into standard basis vectors

theorem Vector_decomposition {n} (s : Vector n) : s = ∑ i, s i 0 • std_basis i
:= begin
    apply matrix.ext,
    intros i j,
    cases j with j jp,
    have jeq: j = 0, {
        linarith,
    },
    cases jeq,
    simp,
    rw finset.sum_eq_single i, {
        simp,
    }, {
        intros b bp h,
        rw std_basis_eq_zero h.symm; simp,
    }, {
        intros c,
        exfalso,
        apply c; simp,
    }
end


------------------------------------------------------------------------------
-- kron_loc lemmas

section kron_loc

variables {n m : ℕ}

@[simp]
lemma kron_loc_composition (x : fin (n*m)): kron_loc (kron_div x) (kron_mod x) = x
:= begin
    unfold kron_div kron_mod kron_loc,
    cases x with x xp,
    simp,
    have f1: 0 < m, {
        cases m, {
            simp at xp,
            exfalso, linarith,
        }, {
            simp,
        }
    },
    symmetry,
    apply nat_decompose_mul_add, assumption,
end

@[simp]
lemma kron_div_kron_loc (k j : fin (n * m)) : kron_div (kron_loc k j) = k
:= begin
    unfold kron_div kron_loc, simp,
    cases k with k kp,
    cases j with j jp,
    simp,
    rw nat_add_mul_left_div_left, {
        rw nat.div_eq_zero; simp *,
    }, {
        linarith,
    }
end

@[simp]
lemma kron_mod_kron_loc (k j : fin (n * m)) : kron_mod (kron_loc k j) = j
:= begin
    unfold kron_mod kron_loc, simp,
    cases k with k kp,
    cases j with j jp,
    simp,
    rw nat_add_mul_left_mod_left, {
        rw nat.mod_eq_of_lt; assumption,
    }
end

lemma kron_loc_inj (a b : fin n) (c d : fin m) : kron_loc a c = kron_loc b d → a = b ∧ c = d
:= begin
    intros h,
    cases a with a ap,
    cases b with b bp,
    cases c with c cp,
    cases d with d dp,
    simp,
    unfold kron_loc at h, simp at h,
    apply add_mul_congr; try {assumption},
end

end kron_loc


---------------------------------------------------------------------------------------------
-- kron lemmas

section kron

variables {m n p q : ℕ}
variables (A : Matrix m n) (B : Matrix p q)

theorem adjoint_kron : (A ⊗ B)† = (A†) ⊗ (B†)
:= begin
    apply matrix.ext,
    intros j i,
    unfold kron,
    unfold Matrix.adjoint,
    simp,
end

theorem mul_to_kron (r : fin m) (s : fin n) (v : fin p) (w : fin q)
        : A r s * B v w = (A ⊗ B) (kron_loc r v) (kron_loc s w)
:= begin
    unfold kron,
    unfold kron_loc,
    unfold kron_div kron_mod,
    cases r with r hr,
    cases s with s hs,
    cases v with v hv,
    cases w with w hw,
    simp,
    congr, {
        rw nat_add_mul_left_div_left,
        rw nat.div_eq_of_lt hv; refl,
        linarith,
    }, {
        rw nat_add_mul_left_div_left,
        rw nat.div_eq_of_lt hw; refl,
        linarith,
    }, {
        rw nat_add_mul_left_mod_left,
        rw nat.mod_eq_of_lt hv,
    }, {
        rw nat_add_mul_left_mod_left,
        rw nat.mod_eq_of_lt hw,
    }
end

theorem kron_ext_mul (M : Matrix (m*p) (n*q))
        : (∀ (r : fin m) (s : fin n) (v : fin p) (w : fin q)
           , A r s * B v w = M (kron_loc r v) (kron_loc s w))
          → A ⊗ B = M
:= begin
    intro h,
    rw <- matrix.ext_iff,
    intros x y,
    unfold kron,
    rw h,
    unfold kron_loc,
    unfold kron_div kron_mod,
    simp,
    congr, {
        cases x with x hx,
        simp,
        rw add_comm,
        apply nat.mod_add_div,
    }, {
        cases y with y hy,
        simp,
        rw add_comm,
        apply nat.mod_add_div,
    }
end

theorem kron_ext_mul_iff {M : Matrix (m*p) (n*q)}
        : A ⊗ B = M
          ↔ (∀ (r : fin m) (s : fin n) (v : fin p) (w : fin q)
           , A r s * B v w = M (kron_loc r v) (kron_loc s w))
:= begin
    split, intros h, {
        intros, rw mul_to_kron, rw h,
    }, {
        apply kron_ext_mul,
    }
end


@[simp]
lemma kron_zero_left {p q m n} {x : Matrix m n} : (0 : Matrix p q) ⊗ x = 0
:= begin
    apply kron_ext_mul, intros r s v w, simp,
end

@[simp]
lemma kron_zero_right {p q m n} {x : Matrix m n} : x ⊗ (0 : Matrix p q) = 0
:= begin
    apply kron_ext_mul, intros r s v w, simp,
end


theorem kron_id : (I m) ⊗ (I n) = I (m * n)
:= begin
    apply kron_ext_mul,
    intros r s v w,
    by_cases h1: r = s, {
        rw <- h1,
        clear h1,
        by_cases h2: v = w, {
            rw <- h2,
            clear h2,
            simp,
        }, {
            have f1: (I n) v w = 0, {
                apply if_neg, exact h2,
            },
            rw f1,
            simp,
            have f2: (kron_loc r v) ≠ (kron_loc r w), {
                unfold kron_loc,
                intro h,
                apply h2,
                rw fin.eq_iff_veq at h,
                simp at h,
                apply fin.coe_injective,
                exact h,
            },
            symmetry,
            apply if_neg,
            exact f2,
        }
    }, {
        have f1: (I m) r s = 0, {
            apply if_neg, exact h1,
        },
        rw f1,
        simp,
        have f2: (kron_loc r v) ≠ (kron_loc s w), {
            unfold kron_loc,
            intro h,
            apply h1,
            rw fin.eq_iff_veq at h,
            cases v with v vh,
            cases w with w wh,
            simp at h,
            cases add_mul_congr h vh wh with e1 e2,
            apply fin.coe_injective,
            exact e1,
        },
        symmetry,
        apply if_neg,
        exact f2,
    }
end

-- kron distributive over addition
theorem kron_dist_over_add_right (C : Matrix p q) : A ⊗ (B + C) = A ⊗ B + A ⊗ C
:= begin
    apply matrix.ext, intros i j,
    unfold kron, simp,
    ring,
end

theorem kron_dist_over_add_left (C : Matrix p q) : (B + C) ⊗ A = B ⊗ A + C ⊗ A
:= begin
    apply matrix.ext, intros i j,
    unfold kron, simp,
    ring,
end

@[simp]
lemma kron_smul_right {s : ℂ} : A ⊗ (s • B) = s • (A ⊗ B)
:= begin
    apply kron_ext_mul, intros r s v w,
    simp,
    rw <- mul_assoc,
    rw mul_comm (A r s),
    rw mul_assoc,
    congr' 1,
    apply mul_to_kron,
end

@[simp]
lemma kron_smul_left {s : ℂ} : (s • A) ⊗ B = s • (A ⊗ B)
:= begin
    apply kron_ext_mul, intros r s v w,
    simp,
    rw mul_assoc,
    congr' 1,
    apply mul_to_kron,
end


lemma kron_id_left : (I 1) ⊗ A = cast (by simp) A
:= begin
    apply matrix.ext, intros i j,
    unfold kron kron_div kron_mod,
    cases i with i ip,
    cases j with j jp,
    simp,
    rw matrix_cast_apply; try {simp},

    have ip': i < m, by linarith,
    have jp': j < n, by linarith,

    congr' 2, {
        rw nat.mod_eq_of_lt ip',
    }, {
        rw nat.mod_eq_of_lt jp',
    },
end

lemma kron_id_right : A ⊗ (I 1) = cast (by simp) A
:= begin
    apply matrix.ext, intros i j,
    unfold kron kron_div kron_mod,
    cases i with i ip,
    cases j with j jp,
    simp,
    rw matrix_cast_apply; try {simp},
    congr' 2,
end

-- Special case of 1 × 1 matrix.
@[simp] lemma kron_one_one : (I 1) ⊗ (I 1) = I 1
:= begin
    rw kron_id_right, refl,
end

-- Special case of 1 × 1 matrix.
@[simp] lemma kron_id_left_square_one (M : Square 1) : (I 1) ⊗ M = M
:= begin
    unfold kron kron_div kron_mod,
    apply matrix.ext, intros i j, simp,
    congr,
end

-- Special case of 1 × 1 matrix.
@[simp] lemma kron_id_right_square_one (M : Square 1) : M ⊗ (I 1) = M
:= begin
    unfold kron kron_div kron_mod,
    apply matrix.ext, intros i j, simp,
end

-- Special case of 1 × 1 matrix.
lemma kron_square_one_eq_mul {x y : Square 1} : x ⊗ y = x ⬝ y
:= begin
    apply matrix.ext, intros i j,
    have i0 : i = ⟨0, by simp⟩, cases i; simp; linarith,
    have j0 : j = ⟨0, by simp⟩, cases j; simp; linarith,
    cases i0, clear i0,
    cases j0, clear j0,
    unfold kron kron_div kron_mod, simp,

    have f1: (x ⬝ y) ⟨0, by simp⟩ ⟨0, by simp⟩ = x 0 0 * y 0 0, {
        simp, apply matrix_mul_square_one,
    },
    rw <- f1, refl,
end

-- Special case of 1 × 1 matrix.
lemma kron_cancel_left {x : Matrix m n} {y z : Square 1} : x ⊗ y = x ⊗ z → x ≠ 0 → y = z
:= begin
    intros h xn,

    apply matrix.ext, intros i j,
    rw <- matrix.ext_iff at h,
    rcases (Matrix_nonzero_has_nonzero_val xn) with ⟨r, ⟨s, h1⟩⟩,
    specialize h ⟨r, by {cases r, linarith}⟩ ⟨s, by {cases s, linarith}⟩,
    unfold kron kron_div kron_mod at h, simp at h,

    cases h, {
        have i0 : i = 0, cases i; simp, cases i0; clear i0,
        have j0 : j = 0, cases j; simp, cases j0; clear j0,
        simp,
        assumption,
    }, {
        exfalso, apply h1, assumption,
    }
end

end kron


----------------------------------------------------------------------------------------
-- theorem kron_std_basis

-- Kronecker product of two standard basis vector is another standard basis vector.
theorem kron_std_basis {n m : ℕ} (i : fin n) (j : fin m)
        : kron (std_basis i) (std_basis j)
          = std_basis ⟨m * (i : ℕ) + (j : ℕ), fin_add_mul_lt i j⟩
:= begin
    apply kron_ext_mul,
    intros r s v w,
    unfold kron_loc,
    by_cases h1: r = i, {
        rw h1,
        simp,
        by_cases h2: v = j, {
            rw h2,
            simp,
        }, {
            rw std_basis_eq_zero h2,
            rw std_basis_eq_zero,
            simp,
            intro c,
            apply h2,
            apply fin.coe_injective,
            exact c,
        }
    }, {
        rw std_basis_eq_zero h1,
        simp,
        rw std_basis_eq_zero,
        simp,
        intro c,
        cases (add_mul_congr c v.property j.property) with f1 f2,
        apply h1,
        apply fin.coe_injective,
        exact f1,
    }
end


------------------------------------------------------------------------------------------------
-- kron assoc

section kron_assoc

variables {m n p q r s: ℕ} (a : Matrix m n) (b : Matrix p q) (c : Matrix r s)

lemma kron_assoc_cast : Matrix ((m * p) * r) ((n * q) * s) = Matrix (m * (p * r)) (n * (q * s))
:= begin
    ring,
end

theorem kron_assoc : a ⊗ (b ⊗ c) = cast kron_assoc_cast ((a ⊗ b) ⊗ c)
:= begin
    apply matrix.ext, intros i j,
    unfold kron,

    cases i with i ip,
    cases j with j jp,
    unfold kron_div kron_mod,
    simp,
    rw matrix_cast_apply; simp <|> skip, {
        rw mul_assoc,
        congr' 3, {
            rw coe_cast_fin; try { solve1 {ring <|> simp} <|> simp },
            ring, symmetry; apply nat.div_div_eq_div_mul,
        }, {
            rw coe_cast_fin; try { solve1 {ring <|> simp} <|> simp },
            ring, symmetry; apply nat.div_div_eq_div_mul,
        }, {
            simp, rw coe_cast_fin; try { solve1 {ring <|> simp} <|> simp },
            apply nat.mod_mul_left_div_self,
        }, {
            simp, rw coe_cast_fin; try { solve1 {ring <|> simp} <|> simp },
            apply nat.mod_mul_left_div_self,
        }, {
            simp, rw coe_cast_fin; try { solve1 {ring <|> simp} <|> simp },
        }, {
            simp, rw coe_cast_fin; try { solve1 {ring <|> simp} <|> simp },
        }
    }, {
        ring,
    }, {
        ring,
    }
end

lemma kron_assoc_l2r : (a ⊗ b) ⊗ c = cast kron_assoc_cast.symm (a ⊗ (b ⊗ c))
:= begin
    rw kron_assoc,
    rw cast_roundtrip,
end

end kron_assoc


------------------------------------------------------------------------------
-- kron_mixed_prod

section kron_sum_mul_mul

variables {α : Type} [comm_semiring α]
variables {n m : ℕ}
variables (f : fin n → α)
variables (g : fin m → α)

def kron_to_prod (i : fin (n * m)) : fin n × fin m := ⟨kron_div i, kron_mod i⟩

lemma kron_to_prod_inj (i j : fin (n * m)) : kron_to_prod i = kron_to_prod j → i = j
:= begin
    cases i with i ih,
    cases j with j jh,
    unfold kron_to_prod kron_div kron_mod, simp, intros p q,
    have f1: (i / m * m) = (j / m * m), {
        exact congr (congr_arg has_mul.mul p) rfl,
    },
    have mp : 0 < m, {
        have f1 : 0 < n * m, {
            linarith,
        },
        apply pos_of_mul_pos_left f1, simp,
    },
    let h1 := nat_decompose_mul_add i mp,
    let h2 := nat_decompose_mul_add j mp,
    rw h1,
    rw h2,
    congr; assumption,
end

lemma kron_sum_mul_mul : (∑ x, f x) * (∑ x, g x) = ∑ (x : fin (n * m)), f (kron_div x) * g (kron_mod x)
:= begin
    rw finset.sum_mul_sum,
    rw <- finset.sum_preimage (λ x : fin (n*m), (⟨kron_div x, kron_mod x⟩ : fin n × fin m)),
    congr, {
        ext; simp,
    }, {
        simp,
        unfold set.inj_on,
        intros,
        apply kron_to_prod_inj,
        assumption,
    }, {
        intros x h1 h2,
        exfalso,
        apply h2, clear h2,
        simp,
        use (m * x.fst + x.snd), {
            cases x,
            simp,
            apply_mod_cast fin_add_mul_lt,
        }, {
            cases x,
            simp,
            unfold kron_div kron_mod,
            simp,
            cases x_fst with i ip,
            cases x_snd with j jp,
            simp,
            split, {
                rw add_comm,
                rw nat.add_mul_div_left,
                rw nat.div_eq_of_lt; assumption <|> simp,
                linarith,
            }, {
                rw add_comm,
                rw nat.add_mod, simp,
                rw nat.mod_eq_of_lt; assumption,
            }
        }
    }
end

end kron_sum_mul_mul

section kron_mixed_prod

variables {n m o : ℕ} (a : Matrix m n) (c : Matrix n o)
variables {q r s : ℕ} (b : Matrix q r) (d : Matrix r s)

theorem kron_mixed_prod : (a ⊗ b) ⬝ (c ⊗ d) = (a ⬝ c) ⊗ (b ⬝ d)
:= begin
    apply matrix.ext, intros i j,
    unfold matrix.mul,
    unfold kron,
    simp,
    unfold matrix.dot_product,
    rw kron_sum_mul_mul,
    congr,
    apply funext, intro x,
    ring,
end

end kron_mixed_prod


------------------------------------------------------------------------------
-- kron + unit lemmas

section unit_kron

variables {n : ℕ} {s : Vector n}
variables {m : ℕ} {t : Vector m}

lemma unit_kron_of_unit : s.unit → t.unit → (s ⊗ t).unit
:= begin
    unfold matrix.unit,
    intros su tu,
    rw adjoint_kron,
    rw kron_mixed_prod,
    rw su,
    rw tu,
    simp,
end

lemma unit_kron_right : (s ⊗ t).unit → s.unit → t.unit
:= begin
    unfold matrix.unit, intros h su,
    rw adjoint_kron at h,
    rw kron_mixed_prod at h,
    rw su at h,
    rw kron_id_left at h,
    apply h,
end

lemma unit_kron_left : (s ⊗ t).unit → t.unit → s.unit
:= begin
    unfold matrix.unit, intros h tu,
    rw adjoint_kron at h,
    rw kron_mixed_prod at h,
    rw tu at h,
    rw kron_id_right at h,
    apply h,
end

end unit_kron


------------------------------------------------------------------------------------------------
-- unitary lemmas

section unitary

variables {n : ℕ} (U: Matrix n n)

lemma unfold_unitary {U : Matrix n n} : U.unitary → (U†) ⬝ U = 1 := by tautology

-- Compatbility with `is_unit U.det`.
lemma unitary_is_unit_det : U.unitary → is_unit U.det
:= begin
    unfold Matrix.unitary,
    intro h,
    apply matrix.is_unit_det_of_left_inverse; assumption,
end

-- Compatbility with `is_unit U`.
lemma unitary_is_unit : U.unitary → is_unit U
:= begin
    intros h,
    rw matrix.is_unit_iff_is_unit_det,
    apply unitary_is_unit_det; assumption,
end

-- Unitary matrix has a right inverse.
lemma unitary_mul_inv_right : U.unitary → U ⬝ U⁻¹ = 1
:= begin
    intro h,
    rw matrix.mul_nonsing_inv,
    apply unitary_is_unit_det; assumption,
end

-- Unitary matrix has a left inverse.
lemma unitary_mul_inv_left : U.unitary → U⁻¹ ⬝ U = 1
:= begin
    intro h,
    rw matrix.nonsing_inv_mul,
    apply unitary_is_unit_det; assumption,
end

-- U† is the inverse.
lemma unitary_inv_eq_adjoint : U.unitary → (U⁻¹) = (U†)
:= begin
    intros h,
    have f1: (U†) ⬝ U ⬝ (U⁻¹) = (U⁻¹), {
        unfold Matrix.unitary at h,
        rw h, simp,
    },
    rw <- f1,
    rw matrix.mul_assoc,
    rw unitary_mul_inv_right; simp <|> assumption,
end

-- Unitary property `U† ⬝ U = 1` can be stated the other way around.
theorem unitary_comm : U.unitary ↔ U ⬝ (U†) = 1
:= begin
    split; intros h; apply matrix.nonsing_inv_left_right; assumption,
end

-- Unitary matrix is also normal.
-- (But, not all normal matrices are unitary.)
theorem unitary_normal : U.unitary → U.normal
:= begin
    unfold Matrix.normal,
    unfold Matrix.unitary,
    intros h,
    rw h,
    symmetry, rw <- unitary_comm, assumption,
end

end unitary

section unitary_and_vector

variables {n : ℕ} (U : Matrix n n)
variables (v : Vector n) (w : Vector n)

-- Unitary operator is norm-preserving.
-- The angle between two quantum states preserves under any unitary operations
theorem unitary_preserve_norm : (U†) ⬝ U = 1 → ((U ⬝ v)†) ⬝ (U ⬝ w) = (v†) ⬝ w
:= begin
    intros up,
    rw adjoint_mul,
    rw <- matrix.mul_assoc,
    rw matrix.mul_assoc (v†),
    rw up; simp [*],
end

-- Unitary matrix presevese the validity of quantum state.
example : (U†) ⬝ U = 1 → (v†) ⬝ v = 1 → ((U ⬝ v)†) ⬝ (U ⬝ v) = 1
:= begin
    intros up pp,
    rw unitary_preserve_norm; assumption,
end

example : U.unitary → ((U ⬝ v)†) ⬝ (U ⬝ w) = (v†) ⬝ w
:= begin
    intros h,
    apply unitary_preserve_norm; assumption,
end

example : U.unitary → (w†) ⬝ w = 1 → ((U ⬝ w)†) ⬝ (U ⬝ w) = 1
:= begin
    intros h wu,
    rw unitary_preserve_norm; assumption,
end

end unitary_and_vector
