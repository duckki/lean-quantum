import quantum
import matrix_lemmas

open_locale big_operators
open matrix
open Matrix
open quantum

------------------------------------------------------------------------------
section measurement

variables {n : ℕ} {s : Vector n}

lemma measure_eq_mul_conj {m : fin n}
        : (measure s m : ℂ) = ((s m 0)†) * (s m 0)
:= begin
    unfold quantum.measure,
    rw <- complex.mul_conj, ring,
end

lemma measure_eq_proj {m : fin n} : (measure s m : ℂ) = proj s m m
:= begin
    unfold quantum.measure proj,
    unfold matrix.mul matrix.dot_product,
    unfold adjoint,
    rw finset.sum_fin_eq_sum_range,
    rw finset.sum_range_one,
    repeat { rw dif_pos }; simp,
end

lemma measure_eq_of_proj_eq {a b : Vector n} :
                   proj a = proj b
    → measure a = measure b
:= begin
    intros h,
    rw <- matrix.ext_iff at h,
    apply funext, intros i,
    have g: (measure a i : ℂ) = measure b i, {
        iterate 2 {rw measure_eq_proj},
        apply h,
    },
    apply_mod_cast g,
end

lemma nonzero_vector_has_nonzero_measure
        : s ≠ 0 → (∃ i, measure s i ≠ 0)
:= begin
    contrapose!,
    intros h,

    apply matrix.ext, intros i j,
    have j0: j = 0, by {simp},
    cases j0, clear j0, simp,

    rw <- complex.norm_sq_eq_zero,
    apply h,
end

end measurement


------------------------------------------------------------------------------
-- proj lemmas

section proj

variables {n : ℕ} {s t : Vector n}

-- `proj s` is self-adjoint (aka "Hermitian").
@[simp]
lemma proj_self_adjoint (s : Vector n) : ((proj s)†) = proj s
:= begin
    unfold proj,
    rw adjoint_mul, simp,
end

lemma proj_mul_adjoint_eq_self {n} {u : Vector n} : u.unit → (proj u)† ⬝ (proj u) = proj u
:= begin
    unfold proj, intros h,
    rw adjoint_mul, simp,
    rw matrix.mul_assoc, congr' 1,
    rw <- matrix.mul_assoc,
    rw unfold_unit h, simp,
end

lemma outer_product_diagnonal_apply {i : fin n}
        : (s ⬝ t†) i i = (s i 0) * (t i 0).conj
:= begin
    unfold matrix.mul adjoint matrix.dot_product,
    rw finset.sum_fin_eq_sum_range,
    rw finset.sum_eq_single 0,
    rw dif_pos; simp,
    simp,
    simp,
end

lemma outer_product_self_diagnonal_apply_eq_norm_sq {i : fin n}
        : (s ⬝ s†) i i = (s i 0).norm_sq
:= begin
    rw outer_product_diagnonal_apply, simp,
end

lemma proj_diagnonal_eq_mul_conj {i : fin n} : s.proj i i = (s i 0)† * s i 0
:= begin
    unfold proj,
    rw outer_product_diagnonal_apply,
    ring,
end

lemma proj_diagnonal_eq_norm_sq {i : fin n} : s.proj i i = (s i 0).norm_sq
:= begin
    rw proj_diagnonal_eq_mul_conj, simp,
end

end proj


section proj_kron

variables {n : ℕ} {s : Vector n}
variables {m : ℕ} {t : Vector m}

lemma proj_kron : proj (s ⊗ t) = proj s ⊗ proj t
:= begin
    unfold proj,
    rw adjoint_kron,
    rw kron_mixed_prod,
end

lemma proj_kron_apply {i : fin n} {j : fin m}
    : proj (s ⊗ t) (kron_loc i j) (kron_loc i j)
      = proj s i i * proj t j j
:= begin
    rw proj_kron,
    cases i with i ip,
    cases j with j jp,
    unfold kron kron_div kron_mod,
    have f1: (m * i + j) / m = i, {
        rw add_comm,
        rw nat.add_mul_div_left,
        rw nat.div_eq_zero jp, simp, linarith,
    },
    have f2: (m * i + j) % m = j, {
        rw add_comm,
        rw nat.add_mul_mod_self_left,
        rw nat.mod_eq_of_lt jp,
    },
    congr' 1, {
        congr; simp; assumption,
    }, {
        congr; simp; assumption,
    }
end

end proj_kron


------------------------------------------------------------------------------
-- proj + std_basis lemmas

section proj_std_basis

variables {n : ℕ} {m : fin n}

lemma proj_std_basis_eq_diagonal
        : proj (std_basis m) = matrix.diagonal (λ i, if i = m then 1 else 0)
:= begin
    unfold proj matrix.mul,
    unfold Matrix.adjoint,
    apply matrix.ext, intros i j,
    simp,
    unfold matrix.dot_product,
    simp,
    by_cases h: i = j, {
        cases h,
        simp,
        by_cases h2: i = m, {
            cases h2,
            simp,
        }, {
            rw if_neg; try {assumption},
            rw std_basis_eq_zero h2,
            simp,
        }
    }, {
        unfold matrix.diagonal,
        rw if_neg h,
        by_cases h2: i = m, {
            have f1: ¬ j = m, by cc,
            rw std_basis_eq_zero f1, simp,
        }, {
            have f1: ¬ i = m, by cc,
            rw std_basis_eq_zero f1, simp,
        }
    }
end

@[simp]
lemma proj_std_basis_eq_one : proj (std_basis m) m m = 1
:= begin
    rw proj_std_basis_eq_diagonal,
    unfold matrix.diagonal, simp,
end

lemma proj_std_basis_eq_zero1 {i j : fin n} : ¬ i = m → proj (std_basis m) i j = 0
:= begin
    rw proj_std_basis_eq_diagonal,
    unfold matrix.diagonal, intros e,
    rw if_neg e, simp,
end

lemma proj_std_basis_eq_zero2 {i j : fin n} : ¬ j = m → proj (std_basis m) i j = 0
:= begin
    rw proj_std_basis_eq_diagonal,
    unfold matrix.diagonal, intros e,
    by_cases h : i = j, {
        cases h, simp, cc,
    }, {
        rw if_neg h,
    }
end

lemma mul_proj_std_basis_left {n} {m : fin n} {U : Square n}
    : proj (std_basis m) ⬝ U = λ i j, ite (i = m) (U i j) 0
:= begin
    apply matrix.ext, intros i j,
    rw proj_std_basis_eq_diagonal,
    rw matrix.diagonal_mul,
    by_cases h: i = m, {
        cases h, clear h, simp,
    }, {
        iterate 2 { rw if_neg h }, simp,
    }
end

lemma mul_proj_std_basis_right {n} {m : fin n} {U : Square n}
    : U ⬝ proj (std_basis m) = λ i j, ite (j = m) (U i j) 0
:= begin
    apply matrix.ext, intros i j,
    rw proj_std_basis_eq_diagonal,
    rw matrix.mul_diagonal,
    by_cases h: j = m, {
        cases h, clear h, simp,
    }, {
        iterate 2 { rw if_neg h }, simp,
    }
end

lemma kron_proj_std_basis {m : fin 2} {U : Square 2}
    : proj (std_basis m) ⊗ U = λ i j, ite (kron_div i = m ∧ kron_div j = m) (U (kron_mod i) (kron_mod j)) 0
:= begin
    apply kron_ext_mul, intros r s v w, simp,
    by_cases h1: r = m, {
        cases h1, clear h1, simp,
        by_cases h2: s = m, {
            cases h2, clear h2, simp,
        }, {
            rw proj_std_basis_eq_zero2 h2,
            rw if_neg h2, simp,
        }
    }, {
        rw proj_std_basis_eq_zero1 h1,
        have : ¬ (r = m ∧ s = m), by cc,
        rw if_neg this, simp,
    }
end

end proj_std_basis


------------------------------------------------------------------------------
-- trace lemmas

section trace

variables {n : ℕ} (v w : Square n)

theorem trace_smul (s : ℂ) : Tr(s • v) = s * Tr(v)
:= begin
    unfold Matrix.trace,
    simp,
    rw finset.mul_sum,
end

lemma trace_adjoint : Tr((v†)) = Tr(v)†
:= begin
    unfold Matrix.trace,
    unfold adjoint,
    rw complex.conj_sum_dist,
end

lemma abs_trace_adjoint : |Tr(v†)| = |Tr(v)|
:= begin
    unfold Matrix.trace,
    unfold adjoint,
    rw complex.conj_sum_dist,
    rw is_R_or_C.abs_conj,
end

lemma trace_mul_comm : Tr(v ⬝ w) = Tr(w ⬝ v)
:= begin
    unfold Matrix.trace,
    unfold matrix.mul matrix.dot_product,
    rw finset.sum_comm,
    congr, apply funext, intros i,
    congr, apply funext, intros j,
    ring,
end

-- for easier match
lemma fin_sum_sum_mul (f : fin n → fin n → ℂ) (g : fin n → ℂ)
        : (∑ (i : fin n), ((∑ (j : fin n), f i j) * (g i)))
        = (∑ (i : fin n) (j : fin n), f i j * g i)
:= begin
    congr, apply funext, intros i,
    rw finset.sum_mul,
end

variables {m : ℕ}

lemma trace_mul_rotate_l (a : Matrix m n) (b : Matrix n m)
        : Tr(a ⬝ v ⬝ b) = Tr(v ⬝ b ⬝ a)
:= begin
    unfold Matrix.trace,
    unfold matrix.mul matrix.dot_product,
    symmetry,
    rw finset.sum_comm,
    congr, apply funext, intros k,
    iterate 2 { rw fin_sum_sum_mul },
    rw finset.sum_comm,
    congr, apply funext, intros i,
    congr, apply funext, intros j,
    ring,
end

theorem trace_kron {x : Square m}: Tr(v ⊗ x) = Tr(v) * Tr(x)
:= begin
    unfold Matrix.trace kron,
    rw kron_sum_mul_mul,
end

end trace

section trace_proj

variables {n : ℕ} (s t : Vector n)

theorem trace_outer_eq_inner : Tr(s ⬝ (t†)) = (t† ⬝ s) 0 0
:= begin
    unfold Matrix.trace,
    unfold matrix.mul,
    unfold matrix.dot_product,
    congr' 1, apply funext, intro x,
    rw finset.sum_fin_eq_sum_range,
    rw finset.sum_range_one,
    rw dif_pos; try { solve1 {simp} },
    simp,
    ring,
end

lemma trace_outer_eq_trace_inner : Tr(s ⬝ (t†)) = Tr((t†) ⬝ s)
:= begin
    rw trace_outer_eq_inner,
    unfold Matrix.trace,
    rw finset.sum_fin_eq_sum_range,
    rw finset.sum_eq_single 0; simp,
end

theorem trace_proj : Tr(proj s) = ((s†) ⬝ s) 0 0
:= begin
    unfold proj,
    rw trace_outer_eq_inner,
end

lemma trace_proj_eq_one_of_unit {s : Vector n} : s.unit → Tr(proj s) = 1
:= begin
    intros h,
    rw trace_proj,
    rw unfold_unit h, simp,
end

lemma trace_proj_eq_one_of_unit' {s : Vector n} : s.unit → Tr(s ⬝ (s†)) = 1
:= begin
    intros h,
    rw trace_outer_eq_inner,
    rw unfold_unit h, simp,
end

lemma unit_of_trace_proj_eq_one : Tr(proj s) = 1 → s.unit
:= begin
    rw trace_proj,
    intros h,
    unfold matrix.unit,
    apply matrix.ext, intros i j,
    have i0 : i = 0, {
        cases i, simp,
    },
    have j0 : j = 0, {
        cases j, simp,
    },
    cases i0,
    cases j0,
    simp, assumption,
end

lemma trace_proj_inner_prod : Tr(proj (s† ⬝ t)) = Tr(proj s ⬝ proj t)
:= begin
    unfold proj,
    rw adjoint_mul, simp,
    rw <- matrix.mul_assoc,
    rw matrix.mul_assoc (s†),
    rw trace_mul_rotate_l,
    rw matrix.mul_assoc,
    rw _root_.trace_mul_comm,
end

lemma conj_trace_outer_product : Tr(s ⬝ t†)† = Tr(s† ⬝ t)
:= begin
    have f1: (t ⬝ s†)† = (s ⬝ t†), {
        rw adjoint_mul, simp,
    },
    rw <- f1,
    rw trace_adjoint, simp,
    apply trace_outer_eq_trace_inner,
end

end trace_proj


------------------------------------------------------------------------------
-- partial_trace lemmas

section partial_trace_add

variables {n m : ℕ} {x y : Square n * m}

lemma partial_trace_add : partial_trace (x + y) = partial_trace x + partial_trace y
:= begin
    unfold partial_trace Matrix.trace,
    apply funext, intros k,
    apply funext, intros i,
    simp,
    rw finset.sum_add_distrib,
end

end partial_trace_add


section partial_trace_kron

variables {n m : ℕ} (v : Square n) (w : Square m)

lemma partial_trace_kron : partial_trace (v ⊗ w) = Tr(w) • v
:= begin
    unfold partial_trace Matrix.trace,
    apply funext, intros k,
    apply funext, intros i,
    simp,
    rw finset.sum_mul,
    congr' 1, apply funext, intros j,
    rw mul_comm,
    rw mul_to_kron,
end

@[simp]
theorem trace_partial_trace {v : Square n*m} : Tr(partial_trace v) = Tr(v)
:= begin
    unfold Matrix.trace partial_trace,
    rw <- finset.sum_preimage (λ x : fin n × fin m, (kron_loc x.fst x.snd : fin (n * m))), {
        rw <- finset.sum_product',
        simp,
        congr' 1,
        ext; simp,
    }, {
        simp,
        unfold set.inj_on,
        intros,
        rw prod.eq_iff_fst_eq_snd_eq,
        apply kron_loc_inj; assumption,
    }, {
        intros x _ h2,
        exfalso,
        apply h2, clear h2,
        use (⟨kron_div x, kron_mod x⟩),
        simp,
    }
end

lemma partial_trace_kron_eq {o} (x : Square o): Tr(v) = Tr(w)
        → partial_trace (x ⊗ v) = partial_trace (x ⊗ w)
:= begin
    intros t,
    iterate 2 { rw partial_trace_kron },
    rw t,
end

lemma partial_trace_kron_neq {o} (x y : Square o): Tr(v) = Tr(w)
        → partial_trace (x ⊗ v) ≠ partial_trace (y ⊗ w)
        → x ≠ y
:= begin
    intros t h c, apply h, clear h,
    cases c, apply partial_trace_kron_eq, assumption,
end

end partial_trace_kron


section partial_trace_proj

variables {n : ℕ} {s t : Vector n}
variables {m : ℕ} {a b : Vector m}

lemma partial_proj_eq_of_kron_eq :
        a ⊗ s = b ⊗ t
        → Tr(proj s) = 1 → Tr(proj t) = 1
        → proj a = proj b
:= begin
    intros h vt wt,
    have f1: partial_trace (proj (a ⊗ s)) = partial_trace (proj (b ⊗ t)), {
        rw h,
    },
    iterate 2 { rw proj_kron at f1 },
    iterate 2 { rw partial_trace_kron at f1 },
    rw vt at f1,
    rw wt at f1,
    simp at f1, assumption,
end

lemma partial_proj_eq_of_kron_eq' :
        a ⊗ s = b ⊗ t
        → s.unit → t.unit
        → proj a = proj b
:= begin
    intros h su tu,
    apply partial_proj_eq_of_kron_eq; try {assumption},
    rw trace_proj, rw unfold_unit su, simp,
    rw trace_proj, rw unfold_unit tu, simp,
end

end partial_trace_proj


section partial_trace_add_kron

variables {n : ℕ} (v w x y : Square n)
variables {m : ℕ} (a b c d : Square m)

lemma partial_trace_add_kron : partial_trace (a ⊗ v + b ⊗ w) = Tr(v) • a + Tr(w) • b
:= begin
    unfold partial_trace Matrix.trace,
    apply funext, intros k,
    apply funext, intros i,
    simp,

    rw finset.sum_add_distrib,
    rw finset.sum_mul,
    rw finset.sum_mul,
    congr' 1, {
        congr' 1, apply funext, intros j,
        rw mul_comm (v j j),
        rw mul_to_kron,
    }, {
        congr' 1, apply funext, intros j,
        rw mul_comm (w j j),
        rw mul_to_kron,
    }
end

lemma partial_trace_add_kron2 : partial_trace (a ⊗ v + b ⊗ w + c ⊗ x + d ⊗ y)
                                = Tr(v) • a + Tr(w) • b + Tr(x) • c + Tr(y) • d
:= begin
    unfold partial_trace Matrix.trace,
    apply funext, intros k,
    apply funext, intros i,
    simp,

    repeat { rw finset.sum_add_distrib },
    repeat { rw finset.sum_mul },
    congr' 1, {
        congr' 1, {
            congr' 1, {
                congr' 1, apply funext, intros j,
                rw mul_comm (v j j),
                rw mul_to_kron,
            }, {
                congr' 1, apply funext, intros j,
                rw mul_comm (w j j),
                rw mul_to_kron,
            }
        }, {
            congr' 1, apply funext, intros j,
            rw mul_comm (x j j),
            rw mul_to_kron,
        }
    }, {
        congr' 1, apply funext, intros j,
        rw mul_comm (y j j),
        rw mul_to_kron,
    }
end

end partial_trace_add_kron


section partial_trace_proj_add_kron

variables {n: ℕ} (s t p: Vector n)
variables {m: ℕ} (v w q: Vector m)

lemma proj_add_kron : proj ((t ⊗ w) + (p ⊗ q))
            = t ⬝ (t†) ⊗ (w ⬝ (w†)) + t ⬝ (p†) ⊗ (w ⬝ (q†)) + p ⬝ (t†) ⊗ (q ⬝ (w†)) + p ⬝ (p†) ⊗ (q ⬝ (q†))
:= begin
    unfold proj, repeat { rw adjoint_add <|> rw adjoint_kron },
    repeat { rw matrix.add_mul <|> rw matrix.mul_add },
    repeat { rw kron_mixed_prod },
    rw <- add_assoc,
end

lemma partial_trace_proj_add_kron : w.unit → q.unit → (w†) ⬝ q = 1
            → partial_trace (proj ((t ⊗ w) + (p ⊗ q))) = proj (t + p)
:= begin
    intros wu qu h,
    rw proj_add_kron,
    rw partial_trace_add_kron2,
    rw trace_proj_eq_one_of_unit' wu,
    rw trace_proj_eq_one_of_unit' qu,

    have f1: Tr(q ⬝ (w†)) = 1, {
        rw trace_outer_eq_inner, rw h, simp,
    },
    have f2: Tr(w ⬝ (q†)) = 1, {
        have h': (q†) ⬝ w = 1, {
            apply adjoint_inj, rw adjoint_mul, simp *,
        },
        rw trace_outer_eq_inner, rw h', simp,
    },
    rw f1, rw f2, simp,

    unfold proj, rw adjoint_add,
    repeat { rw matrix.add_mul <|> rw matrix.mul_add },
    abel,
end

lemma partial_trace_proj_add_kron2 : w.unit → q.unit → (w†) ⬝ q = 0
            → partial_trace (proj ((t ⊗ w) + (p ⊗ q))) = proj t + proj p
:= begin
    intros wu qu h,
    rw proj_add_kron,
    rw partial_trace_add_kron2,
    rw trace_proj_eq_one_of_unit' wu,
    rw trace_proj_eq_one_of_unit' qu,
    have f1: Tr(q ⬝ (w†)) = 0, {
        rw trace_outer_eq_inner, rw h, simp,
    },
    have f2: Tr(w ⬝ (q†)) = 0, {
        have h': (q†) ⬝ w = 0, {
            apply adjoint_inj, rw adjoint_mul, simp *,
        },
        rw trace_outer_eq_inner, rw h', simp,
    },
    rw f1, rw f2, unfold proj, simp,
end

end partial_trace_proj_add_kron


------------------------------------------------------------------------------
-- state_after_measure lemmas

section state_after_measure_lemmas

variables {n : ℕ} {s : Vector n} {m : fin n}

lemma state_after_measure_eq_zero {i : fin n}
        : ¬ i = m → (state_after_measure s m) i 0 = 0
:= begin
    unfold quantum.measure state_after_measure,
    intros h,
    rw Matrix.real_smul_apply,
    rw matrix.mul_apply,
    rw finset.sum_eq_zero; try {solve1 {simp}},
    intros x xh,
    rw proj_std_basis_eq_zero1; simp [*],
end

lemma abs_state_after_measure_eq_one {i : fin n}
        : ⟦s⟧ m ≠ 0 → i = m → |state_after_measure s m i 0| = 1
:= begin
    intros sp h, cases h, clear h,
    unfold quantum.measure state_after_measure,
    rw Matrix.real_smul_apply,
    rw matrix.mul_apply,
    rw finset.sum_eq_single m, {
        simp, ring,
        rw <- is_R_or_C.norm_sq_to_complex,
        rw is_R_or_C.sqrt_norm_sq_eq_norm,
        simp,
        rw mul_inv_cancel, {
            intro c,
            apply sp, clear sp,
            unfold quantum.measure,
            rw complex.norm_sq_eq_abs,
            rw c, simp,
        }
    }, {
        intros x xp xh,
        rw proj_std_basis_eq_zero2; simp [*],
    }, {
        simp,
    }
end

lemma measure_state_after_measure_eq_one {i : fin n}
        : ⟦s⟧ m ≠ 0 → i = m → measure (state_after_measure s m) i = 1
:= begin
    intros sp h, cases h, clear h,
    unfold quantum.measure state_after_measure,
    rw Matrix.real_smul_apply,
    rw matrix.mul_apply,
    rw finset.sum_eq_single m, {
        simp, ring,
        rw mul_inv_cancel, {
            intro c,
            apply sp, clear sp,
            apply c,
        }
    }, {
        intros x xp xh,
        rw proj_std_basis_eq_zero2; simp [*],
    }, {
        simp,
    }
end

lemma measure_state_after_measure_eq_measure_std_basis
        : ⟦s⟧ m ≠ 0 → measure (state_after_measure s m) = measure (std_basis m)
:= begin
    intros h,
    ext1 i,
    by_cases c: i = m, {
        cases c, clear c,
        rw measure_state_after_measure_eq_one h rfl,
        unfold quantum.measure, simp,
    }, {
        unfold quantum.measure,
        rw state_after_measure_eq_zero c,
        rw std_basis_eq_zero c,
    },
end

end state_after_measure_lemmas


------------------------------------------------------------------------------
-- partial measure lemmas

section partial_measure

variables {n : ℕ} {a b : Vector n}
variables {m : ℕ} {s t : Vector m}

lemma measure_eq_of_kron_eq :
        a ⊗ s = b ⊗ t
        → Tr(proj s) = 1 → Tr(proj t) = 1
        → measure a = measure b
:= begin
    intros h su tu,
    apply measure_eq_of_proj_eq,
    apply partial_proj_eq_of_kron_eq h; assumption,
end

-- not true
-- example: a ⊗ (s + t) = b ⊗ (v + w)
--         → Tr(proj (s + t)) = 1 → Tr(proj (v + w)) = 1
--         → proj a = proj b

lemma partial_measure_proj_kron
        : Tr(proj s) = 1
        → partial_measure (a ⊗ s) = measure a
:= begin
    intros vu,
    apply funext, intros i,
    unfold partial_measure quantum.measure,
    rw proj_kron,
    rw partial_trace_kron,
    rw vu, simp,
    rw proj_diagnonal_eq_norm_sq, simp,
    rw _root_.abs_of_nonneg, simp,
end

lemma partial_measure_eq_of_kron_eq :
        a ⊗ s = b ⊗ t
        → Tr(proj s) = 1 → Tr(proj t) = 1
        → measure a = measure b
:= begin
    intros h stu vwu,
    have f1: partial_measure (a ⊗ s) = partial_measure (b ⊗ t), {
        rw h,
    },
    rw partial_measure_proj_kron stu at f1,
    rw partial_measure_proj_kron vwu at f1,
    assumption,
end

lemma unit_has_nonzero_measure
        : s.unit → (∃ i, measure s i ≠ 0)
:= begin
    intros h,
    apply nonzero_vector_has_nonzero_measure,
    apply unit_nonzero, assumption,
end

lemma measure_kron_apply {i : fin n} {j : fin m}
    : measure (a ⊗ s) (kron_loc i j)
      = measure a i * measure s j
:= begin
    have goal: (measure (a ⊗ s) (kron_loc i j) : ℂ)
                = measure a i * measure s j, {
          repeat { rw measure_eq_proj },
          apply proj_kron_apply,
    },
    apply_mod_cast goal,
end

lemma measure_kron_cancel_right:
            measure (a ⊗ s) = measure (b ⊗ s)
            → s.unit
            → measure a = measure b
:= begin
    intros h su,
    apply funext, intro i,
    rw function.funext_iff at h,
    rcases (unit_has_nonzero_measure su) with ⟨j, jp⟩,
    specialize (h (kron_loc i j)),
    iterate 2 {rw measure_kron_apply at h},
    apply mul_right_cancel' _ h; assumption,
end

lemma measure_kron_cancel_left:
            measure (s ⊗ a) = measure (s ⊗ b)
            → s.unit
            → measure a = measure b
:= begin
    intros h su,
    apply funext, intro i,
    rw function.funext_iff at h,
    rcases (unit_has_nonzero_measure su) with ⟨j, jp⟩,
    specialize (h (kron_loc j i)),
    iterate 2 {rw measure_kron_apply at h},
    apply mul_left_cancel' _ h; assumption,
end

end partial_measure


------------------------------------------------------------------------------
-- partial_measure_add_kron

section partial_measure_add_kron

variables {n : ℕ} {a b : Vector n}
variables {m : ℕ} {s t : Vector m}

lemma partial_measure_add_kron_rhs {a b k : ℂ}
        : ((a + b).norm_sq : ℂ) - (2 * ((1 - k) * (a * b†)).re : ℝ)
            = (a.norm_sq + b.norm_sq : ℂ) + (2 * (k * (a * b.conj)).re : ℝ)
:= begin
    have l1: ((a + b).norm_sq : ℂ)
                = (a.norm_sq + b.norm_sq)
                    + (2 * (a * b.conj).re : ℝ), {
        rw <- complex.conj_mul' (a + b),
        repeat { rw complex.conj.map_add },
        repeat { rw add_mul },
        repeat { rw mul_add },
        have l1_1: a * b.conj + b * a.conj
                = (2 * (a * b.conj).re : ℝ), {
            rw <- complex.add_conj,
            congr, simp, ring,
        },
        rw <- l1_1, clear l1_1,
        simp, ring,
    },
    rw l1, clear l1,

    rw add_sub_assoc (a.norm_sq + b.norm_sq : ℂ),
    congr' 1,
    repeat { rw sub_mul },
    repeat { rw two_mul },
    rw complex.sub_re,
    rw is_R_or_C.conj_to_complex,
    norm_cast, ring,
    rw <- sub_sub,
    rw <- sub_add,
    rw <- sub_add,
    repeat { rw <- mul_assoc },
    ring,
end

lemma partial_measure_add_kron : Tr(proj s) = 1 → Tr(proj t) = 1
        → ⦃ a ⊗ s + b ⊗ t ⦄
            = λ i, |(a i 0 + b i 0).norm_sq
                    - 2 * ((1 - Tr(s ⬝ t†)) * (a i 0 * (b i 0)†)).re|
:= begin
    intros su tu,
    ext i,

    have lhs: ⦃a ⊗ s + b ⊗ t⦄ i
                = |((a ⬝ a†) i i + (b ⬝ b†) i i) + (Tr(s ⬝ t†) • ((a ⬝ b†) i i) + Tr(t ⬝ s†) • ((b ⬝ a†) i i))|,
    {
        unfold partial_measure,
        rw proj_add_kron,
        repeat { rw partial_trace_add },
        repeat { rw partial_trace_kron },
        unfold proj at su,
        unfold proj at tu,
        rw su, rw tu,
        simp,
        congr' 1,
        ring,
    },
    rw lhs, clear lhs,
    iterate 2 { rw outer_product_self_diagnonal_apply_eq_norm_sq },
    iterate 2 { rw outer_product_diagnonal_apply },

    have rhs: (((a i 0 + b i 0).norm_sq - 2 * ((1 - Tr(s ⬝ t†)) * (a i 0 * (b i 0)†)).re : ℝ) : ℂ)
            = ((a i 0).norm_sq + (b i 0).norm_sq : ℂ)
                    + (2 * (Tr(s ⬝ t†) * (a i 0 * (b i 0).conj)).re : ℝ), {
        apply_mod_cast partial_measure_add_kron_rhs,
    },
    rw complex.abs_of_real',
    rw rhs,

    congr' 1,
    congr' 1,

    have f1: Tr(s ⬝ t†) * (a i 0 * (b i 0).conj) + Tr(t ⬝ s†) * (b i 0 * (a i 0).conj)
           = (2 * (Tr(s ⬝ t†) * (a i 0 * (b i 0).conj)).re : ℝ), {
        rw <- complex.add_conj,
        simp,
        congr' 1, {
            rw <- adjoint_involutive t,
            rw <- adjoint_mul,
            rw trace_adjoint,
            simp,
        }, {
            ring,
        }
    },
    apply f1,
end

lemma partial_measure_add_kron' : Tr(proj s) = 1 → Tr(proj t) = 1
        → ⦃ a ⊗ s + b ⊗ t ⦄
            = λ i, |(a i 0 + b i 0).norm_sq
                    - 2 * ((1 - Tr(s† ⬝ t)) * ((a i 0)† * b i 0)).re|
:= begin
    intros su tu,
    rw partial_measure_add_kron su tu,
    ext i,

    have f1: ((1 - Tr(s ⬝ t†)) * (a i 0 * (b i 0)†)).re
                = ((1 - Tr(s† ⬝ t)) * ((a i 0)† * b i 0)).re, {
        rw <- complex.re_conj_eq_re,
        congr' 1,
        simp,
        left,
        rw <- is_R_or_C.conj_to_complex,
        rw conj_trace_outer_product,
    },
    rw f1,
end

lemma partial_measure_add_kron_of_orthogonal : Tr(proj s) = 1 → Tr(proj t) = 1
        → (∀ i, (a i 0)† * b i 0 = 0)
        → ⦃ a ⊗ s + b ⊗ t ⦄ = ⟦ a + b ⟧
:= begin
    intros su tu h,
    rw partial_measure_add_kron' su tu,
    ext i,
    rw h, simp,
    unfold quantum.measure,
    apply _root_.abs_of_nonneg, simp,
end

end partial_measure_add_kron


------------------------------------------------------------------------------
-- std_basis lemmas for proof automation

meta def solve_std_basis_zero := `[rw std_basis_eq_zero, dec_trivial]

@[simp] lemma std_basis_0_2_1 : (std_basis 0 : Vector 2) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_1_2_0 : (std_basis 1 : Vector 2) 0 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_0_4_1 : (std_basis 0 : Vector 4) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_0_4_2 : (std_basis 0 : Vector 4) 2 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_0_4_3 : (std_basis 0 : Vector 4) 3 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_1_4_0 : (std_basis 1 : Vector 4) 0 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_1_4_2 : (std_basis 1 : Vector 4) 2 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_1_4_3 : (std_basis 1 : Vector 4) 3 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_2_4_0 : (std_basis 2 : Vector 4) 0 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_2_4_1 : (std_basis 2 : Vector 4) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_2_4_3 : (std_basis 2 : Vector 4) 3 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_3_0_1 : (std_basis 3 : Vector 4) 0 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_3_4_1 : (std_basis 3 : Vector 4) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_3_4_2 : (std_basis 3 : Vector 4) 2 0 = 0 := by solve_std_basis_zero


------------------------------------------------------------------------------
-- More proof automation lemmas related to "fin" type.

@[instance]
def fin_has_zero_one_by_one : has_zero (fin (1 * 1))
:= by {split, exact ⟨0, by dec_trivial⟩}

@[instance]
def fin_has_zero_two_by_two : has_zero (fin (2 * 2))
:= by {split, exact ⟨0, by dec_trivial⟩}

@[instance]
def fin_has_one_two_by_two : has_one (fin (2 * 2))
:= by {split, exact ⟨1, by dec_trivial⟩}


@[simp] lemma fin_one_succ : (⟨(1 : ℕ).succ, by dec_trivial⟩ : fin 4) = ⟨2, by dec_trivial⟩ := by norm_num
@[simp] lemma fin_one_succ_succ : (⟨(1 : ℕ).succ.succ, by dec_trivial⟩ : fin 4) = ⟨3, by dec_trivial⟩ := by norm_num

@[simp] lemma fin_0_div_1 : (⟨(0 : fin 1) / 2, by dec_trivial⟩ : fin 2) = ⟨0, by dec_trivial⟩ := by norm_num
@[simp] lemma fin_0_mod_1 : (⟨(0 : fin 1) % 2, by dec_trivial⟩ : fin 2) = ⟨0, by dec_trivial⟩ := by norm_num
@[simp] lemma fin_0_div_2' : (⟨(0 : fin (2*2)) / 2, by dec_trivial⟩ : fin 2) = ⟨0, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_0_mod_2' : (⟨(0 : fin (2*2)) % 2, by dec_trivial⟩ : fin 2) = ⟨0, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_1_div_2 : (⟨1 / 2, by dec_trivial⟩ : fin 2) = ⟨0, by dec_trivial⟩ := by norm_num
@[simp] lemma fin_1_div_2' : (⟨(1 : fin (2*2)) / 2, by dec_trivial⟩ : fin 2) = ⟨0, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_1_mod_2 : (⟨(1 : fin (2*2)) % 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_2_div_2' : (⟨(2 : fin (2*2)) / 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_2_mod_2' : (⟨(2 : fin (2*2)) % 2, by dec_trivial⟩ : fin 2) = ⟨0, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_3_div_2 : (⟨(3 : fin (3+1)) / 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_3_mod_2 : (⟨(3 : fin (3+1)) % 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_3_div_2' : (⟨(3 : fin (2*2)) / 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_3_mod_2' : (⟨(3 : fin (2*2)) % 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast

@[simp] lemma fin_one_succ_succ_div_2' : (⟨(1 : ℕ).succ.succ / 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast
@[simp] lemma fin_one_succ_succ_mod_2' : (⟨(1 : ℕ).succ.succ % 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_cast


------------------------------------------------------------------------------
-- dot_product proof automation

meta def finish_complex_arith :=
    `[ repeat { simp
            <|> rw_mod_cast complex.conj_of_real
            <|> rw_mod_cast real.sqr_sqrt
            <|> refl
            <|> dec_trivial
            <|> ring
            <|> linarith
        }]

meta def grind_dot_product :=
    `[
        try {unfold matrix.mul matrix.dot_product},
        try {unfold Matrix.adjoint},
        rw finset.sum_fin_eq_sum_range,
        repeat { rw finset.sum_range_succ },
        rw finset.sum_range_zero,
        repeat { rw dif_pos }]


------------------------------------------------------------------------------
-- matrix proof automation

meta def finish_fin_out_of_range_h (h : expr) : tactic unit
:= do
    t ← tactic.infer_type h,
    match t with
    | `(_ < _) :=
        tactic.solve1 (do
            `[exfalso],
            e ← tactic.to_expr ``(not_le_of_gt %%h),
            tactic.apply e,
            `[repeat {rw <- nat.add_one}; linarith])
    | _ := tactic.fail ()
    end

meta def finish_fin_out_of_range : tactic unit
:= do
    ctx ← tactic.local_context,
    ctx.mfirst (λ h, finish_fin_out_of_range_h h)

meta def maybe_numeral (h : expr) : tactic bool
:= do
    match h with
    | (expr.var _) := return false
    | (expr.app _ _) := return true -- maybe
    | _ := return false
    end

meta def find_local_const : expr → tactic expr
| h := do
    match h with
    | (expr.local_const _ _ _ _) := return h
    | `(nat.succ %%h') :=
        do {
            r ← find_local_const h',
            return r
        }
    | _ := tactic.fail ()
    end

meta def destruct_fin_one (h : expr) : tactic unit
:= do
    t ← tactic.infer_type h,
    match t with
    | `(fin has_one.one) := tactic.cases h list.nil >> return ()
    | `(%%x < has_one.one) :=
        do
            c ← find_local_const x,
            tactic.cases c list.nil >> return ()
    | _ := tactic.fail ()
    end

meta def destruct_fin_succ (h : expr) : tactic unit
:= do
    t ← tactic.infer_type h,
    match t with
    | `(fin (nat.succ %%n)) := tactic.cases h list.nil >> return ()
    | `(fin (bit0 %%n)) := tactic.cases h list.nil >> return ()
    | `(%%x < (nat.succ %%y)) :=
        do  c ← find_local_const x,
            tactic.cases c list.nil >> return ()
    | `(%%x < (bit0 %%y)) :=
        do  c ← find_local_const x,
            tactic.cases c list.nil >> return ()
    | _ := tactic.fail ()
    end

-- case-split on a concrete finite set (such as fin 2, n < 3)
meta def destruct_fin : tactic unit
:= do
    ctx ← tactic.local_context,
    finish_fin_out_of_range
    <|> ctx.mfirst (λ h, destruct_fin_one h)
    <|> ctx.mfirst (λ h, destruct_fin_succ h)

-- case split on all matrix coordinates
meta def grind_matrix : tactic unit
:= do
    `[apply matrix.ext, intros],
    `[repeat { destruct_fin }]

meta def unfold_qubits : tactic unit
:= do
    `[try {unfold ket0 ket1}],
    `[try {unfold ket00 ket01 ket10 ket11}],
    `[try {unfold ket_plus ket_minus}]


------------------------------------------------------------------------------
-- state lemmas

@[simp] lemma ket0_unit : |0⟩† ⬝ |0⟩ = 1 := by {unfold_qubits, simp}
@[simp] lemma ket1_unit : |1⟩† ⬝ |1⟩ = 1 := by {unfold_qubits, simp}

meta def unit_vector : tactic unit
:= `[apply matrix.ext; intros; unfold_qubits; grind_dot_product; finish_complex_arith]

@[simp] lemma ket_plus_unit : (|+⟩†) ⬝ |+⟩ = 1 := by unit_vector
@[simp] lemma ket_minus_unit : (|-⟩†) ⬝ |-⟩ = 1 := by unit_vector

meta def solve_vector_eq := `[unfold_qubits; grind_matrix; `[simp]]

lemma ket_plus_alt_def : |+⟩ = (/√2 • |0⟩) + (/√2 • |1⟩) := by solve_vector_eq
lemma ket_minus_alt_def : |-⟩ = (/√2 • |0⟩) + (-/√2 • |1⟩) := by solve_vector_eq

@[simp] lemma ket_zeros_unit {n : ℕ} : (((ket_zeros n)†) ⬝ (ket_zeros n) = 1)
:= by {unfold ket_zeros, simp}

@[simp] lemma ket_phi_plus_unit : ket_phi_plus† ⬝ ket_phi_plus = 1
:= by {unfold ket_phi_plus, unit_vector}

@[simp]
lemma vec_head_fin_one (f : fin 1 → ℂ) : vec_head (λ x : fin 1, f x) = f 0
:= by refl

lemma ket_phi_plus_alt_def : ket_phi_plus = /√2 • (|00⟩) + /√2 • (|11⟩)
:= begin
    unfold ket_phi_plus,
    solve_vector_eq,
end

lemma ket_phi_plus_alt_def' : ket_phi_plus = /√2 • (|0⟩ ⊗ |0⟩) + /√2 • (|1⟩ ⊗ |1⟩)
:= begin
    rw ket_phi_plus_alt_def,
    unfold ket0 ket1 ket00 ket11,
    repeat { rw kron_std_basis },
    congr,
end

-- The "unit" flavor (`s.unit`), instead of `s† ⬝ s`.
@[simp] lemma ket0_unit': |0⟩.unit := by {unfold ket0, simp}
@[simp] lemma ket1_unit': |1⟩.unit := by {unfold ket1, simp}
@[simp] lemma ket_plus_unit': |+⟩.unit := by {unfold matrix.unit, simp}
@[simp] lemma ket_minus_unit': |-⟩.unit := by {unfold matrix.unit, simp}


------------------------------------------------------------------------------------------------
-- Inner product values

-- This could be read as `⟨0|+⟩` on books.
@[simp] lemma inner_ket0_ket_plus :  ⟪ |0⟩, |+⟩ ⟫ = (/√2 : ℂ)
:= begin
    unfold has_inner.inner Matrix.inner_product,
    unfold_qubits; grind_dot_product; finish_complex_arith,
end


------------------------------------------------------------------------------------------------
-- gate lemmas

meta def unfold_gates := `[try {unfold X Z H CNOT CZ SWAP}]
meta def solve_matrix_mul := `[unfold_gates; unfold_qubits; grind_matrix; grind_dot_product; finish_complex_arith]

@[simp] lemma X_unitary : X† ⬝ X = 1 := by solve_matrix_mul
@[simp] lemma Z_unitary : Z† ⬝ Z = 1 := by solve_matrix_mul
@[simp] lemma H_unitary : H† ⬝ H = 1 := by solve_matrix_mul

meta def solve_matrix_apply_eq := `[unfold_gates; grind_dot_product; finish_complex_arith]

@[simp] lemma CNOT_self_inner_0_0 : (CNOT† ⬝ CNOT) 0 0 = 1 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_0_1 : (CNOT† ⬝ CNOT) 0 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_0_2 : (CNOT† ⬝ CNOT) 0 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_0_3 : (CNOT† ⬝ CNOT) 0 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma CNOT_self_inner_1_0 : (CNOT† ⬝ CNOT) 1 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_1_1 : (CNOT† ⬝ CNOT) 1 1 = 1 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_1_2 : (CNOT† ⬝ CNOT) 1 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_1_3 : (CNOT† ⬝ CNOT) 1 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma CNOT_self_inner_2_0 : (CNOT† ⬝ CNOT) 2 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_2_1 : (CNOT† ⬝ CNOT) 2 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_2_2 : (CNOT† ⬝ CNOT) 2 2 = 1 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_2_3 : (CNOT† ⬝ CNOT) 2 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma CNOT_self_inner_3_0 : (CNOT† ⬝ CNOT) 3 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_3_1 : (CNOT† ⬝ CNOT) 3 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_3_2 : (CNOT† ⬝ CNOT) 3 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma CNOT_self_inner_3_3 : (CNOT† ⬝ CNOT) 3 3 = 1 := by solve_matrix_apply_eq

@[simp] lemma CNOT_unitary : CNOT† ⬝ CNOT = 1 := by {grind_matrix; finish_complex_arith}


@[simp] lemma CZ_inner_self_0_0 : (CZ† ⬝ CZ) 0 0 = 1 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_0_1 : (CZ† ⬝ CZ) 0 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_0_2 : (CZ† ⬝ CZ) 0 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_0_3 : (CZ† ⬝ CZ) 0 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma CZ_inner_self_1_0 : (CZ† ⬝ CZ) 1 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_1_1 : (CZ† ⬝ CZ) 1 1 = 1 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_1_2 : (CZ† ⬝ CZ) 1 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_1_3 : (CZ† ⬝ CZ) 1 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma CZ_inner_self_2_0 : (CZ† ⬝ CZ) 2 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_2_1 : (CZ† ⬝ CZ) 2 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_2_2 : (CZ† ⬝ CZ) 2 2 = 1 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_2_3 : (CZ† ⬝ CZ) 2 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma CZ_inner_self_3_0 : (CZ† ⬝ CZ) 3 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_3_1 : (CZ† ⬝ CZ) 3 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_3_2 : (CZ† ⬝ CZ) 3 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma CZ_inner_self_3_3 : (CZ† ⬝ CZ) 3 3 = 1 := by solve_matrix_apply_eq

lemma CZ_unitary : CZ† ⬝ CZ = 1 := by {grind_matrix; finish_complex_arith}


@[simp] lemma SWAP_inner_self_0_0 : (SWAP† ⬝ SWAP) 0 0 = 1 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_0_1 : (SWAP† ⬝ SWAP) 0 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_0_2 : (SWAP† ⬝ SWAP) 0 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_0_3 : (SWAP† ⬝ SWAP) 0 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma SWAP_inner_self_1_0 : (SWAP† ⬝ SWAP) 1 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_1_1 : (SWAP† ⬝ SWAP) 1 1 = 1 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_1_2 : (SWAP† ⬝ SWAP) 1 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_1_3 : (SWAP† ⬝ SWAP) 1 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma SWAP_inner_self_2_0 : (SWAP† ⬝ SWAP) 2 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_2_1 : (SWAP† ⬝ SWAP) 2 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_2_2 : (SWAP† ⬝ SWAP) 2 2 = 1 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_2_3 : (SWAP† ⬝ SWAP) 2 3 = 0 := by solve_matrix_apply_eq

@[simp] lemma SWAP_inner_self_3_0 : (SWAP† ⬝ SWAP) 3 0 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_3_1 : (SWAP† ⬝ SWAP) 3 1 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_3_2 : (SWAP† ⬝ SWAP) 3 2 = 0 := by solve_matrix_apply_eq
@[simp] lemma SWAP_inner_self_3_3 : (SWAP† ⬝ SWAP) 3 3 = 1 := by solve_matrix_apply_eq

lemma SWAP_unitary : SWAP† ⬝ SWAP = 1 := by {grind_matrix; finish_complex_arith}


------------------------------------------------------------------------------
-- gate and state lemmas

@[simp] lemma X_ket0_eq_ket1 : X ⬝ |0⟩ = |1⟩ := by solve_matrix_mul
@[simp] lemma X_ket1_eq_ket0 : X ⬝ |1⟩ = |0⟩ := by solve_matrix_mul

@[simp] lemma H_ket0_eq_ket_plus  : H ⬝ |0⟩ = |+⟩ := by solve_matrix_mul
@[simp] lemma H_ket1_eq_ket_minus : H ⬝ |1⟩ = |-⟩ := by solve_matrix_mul
@[simp] lemma H_ket_plus_eq_ket0  : H ⬝ |+⟩ = |0⟩ := by solve_matrix_mul
@[simp] lemma H_ket_minus_eq_ket1 : H ⬝ |-⟩ = |1⟩ := by solve_matrix_mul

@[simp] lemma CNOT_ket00_eq_ket00 : CNOT ⬝ |00⟩ = |00⟩ := by solve_matrix_mul
@[simp] lemma CNOT_ket01_eq_ket01 : CNOT ⬝ |01⟩ = |01⟩ := by solve_matrix_mul
@[simp] lemma CNOT_ket10_eq_ket11 : CNOT ⬝ |10⟩ = |11⟩ := by solve_matrix_mul
@[simp] lemma CNOT_ket11_eq_ket10 : CNOT ⬝ |11⟩ = |10⟩ := by solve_matrix_mul


------------------------------------------------------------------------------
-- SWAP gate lemmas

section SWAP_lemmas

variables {a b : Vector 2}

meta def unfold_swap_app := `[unfold SWAP; simp; unfold matrix.vec_head matrix.vec_tail]
meta def solve_swap_kron := unfold_swap_app; `[unfold kron kron_div kron_mod; repeat {simp <|> ring}]

lemma SWAP_kron_0 : (SWAP ⬝ (a ⊗ b)) ⟨0, by dec_trivial⟩ ⟨0, by dec_trivial⟩ = (b ⊗ a) 0 0
:= by solve_swap_kron
lemma SWAP_kron_1 : (SWAP ⬝ (a ⊗ b)) ⟨1, by dec_trivial⟩ ⟨0, by dec_trivial⟩ = (b ⊗ a) 1 0
:= by solve_swap_kron
lemma SWAP_kron_2 : (SWAP ⬝ (a ⊗ b)) ⟨2, by dec_trivial⟩ ⟨0, by dec_trivial⟩ = (b ⊗ a) 2 0
:= by solve_swap_kron
lemma SWAP_kron_3 : (SWAP ⬝ (a ⊗ b)) ⟨3, by dec_trivial⟩ ⟨0, by dec_trivial⟩ = (b ⊗ a) 3 0
:= by solve_swap_kron

@[simp] lemma SWAP_kron_0' : (SWAP ⬝ (a ⊗ b)) (⟨0, by dec_trivial⟩ : fin (2*2)) ⟨0, by dec_trivial⟩
                             = (b ⊗ a) 0 0
:= by apply SWAP_kron_0

@[simp] lemma SWAP_kron_1' : (SWAP ⬝ (a ⊗ b)) (⟨1, by dec_trivial⟩ : fin (2*2)) ⟨0, by dec_trivial⟩
                             = (b ⊗ a) 1 0
:= by apply SWAP_kron_1

@[simp] lemma SWAP_kron_2' : (SWAP ⬝ (a ⊗ b)) (bit0 (⟨1, by dec_trivial⟩ : fin (2*2))) ⟨0, by dec_trivial⟩
                             = (b ⊗ a) 2 0
:= by apply SWAP_kron_2

@[simp] lemma SWAP_kron_3' : (SWAP ⬝ (a ⊗ b)) (⟨2 + 1, by dec_trivial⟩ : fin (2*2)) ⟨0, by dec_trivial⟩
                             = (b ⊗ a) 3 0
:= by apply SWAP_kron_3

lemma SWAP_kron : SWAP ⬝ (a ⊗ b) = b ⊗ a
:= begin
    symmetry,
    apply kron_ext_mul, intros r s v w,
    unfold kron_loc,
    repeat { destruct_fin }; {
        simp, unfold kron kron_div kron_mod, simp,
    },
end

end SWAP_lemmas


------------------------------------------------------------------------------
-- Numeric constants lemmas for proof automation

@[simp] lemma sqrt_2_nonneg : 0 ≤ √2 := by {apply real.sqrt_nonneg}

@[simp] lemma one_lt_sqrt_2 : 1 < √2
:= begin
    apply real.lt_of_lt_pow_two; try {solve1 {simp <|> linarith}},
    {
        repeat {rw pow_two}, simp,
        rw <- real.sqrt_mul,
        rw real.sqrt_mul_self; linarith,
        linarith,
    },
end

@[simp] lemma sqrt_2_nonzero : √2 ≠ 0
:= by linarith [one_lt_sqrt_2]

@[simp] lemma sqrt_two_mul_self : √2 * √2 = 2
:= by {rw real.mul_self_sqrt, linarith}

@[simp] lemma one_over_sqrt_two_mul_self : /√2 * /√2 = 1/2
:= begin
    rw div_mul_div,
    congr' 1,
    simp,
    rw_mod_cast real.mul_self_sqrt; simp,
end

@[simp] lemma sqrt_two_inv_mul_self : (√2)⁻¹ * (√2)⁻¹ = 1/2
:= by {rw <- mul_inv'; simp}


------------------------------------------------------------------------------
-- Gate decompositions

lemma P0_eq_proj_ket0 : P0 = proj |0⟩
:= begin
    unfold ket0 P0,
    rw proj_std_basis_eq_diagonal,
    grind_matrix; `[simp],
end

lemma P1_eq_proj_ket1 : P1 = proj |1⟩
:= begin
    unfold ket1 P1,
    rw proj_std_basis_eq_diagonal,
    grind_matrix; `[simp],
end

lemma I_eq_add_P0_P1 : (I 2) = P0 + P1
:= begin
    unfold P0 P1,
    grind_matrix; `[simp],
end

lemma I_eq_add_P_plus_P_minus : (I 2) = P_plus + P_minus
:= begin
    unfold X P_plus P_minus,
    grind_matrix; `[simp; ring],
end

lemma X_eq_sub_P_plus_P_minus : X = P_plus - P_minus
:= begin
    unfold X P_plus P_minus,
    grind_matrix; `[simp; ring],
end

lemma Z_eq_sub_P0_P1 : Z = P0 - P1
:= begin
    unfold Z P0 P1,
    grind_matrix; `[simp],
end

lemma CNOT_decompose : CNOT = P0 ⊗ (I 2) + P1 ⊗ X
:= begin
    have r1 : P0 ⊗ (I 2) = λ (i j : fin (2*2)), ite (kron_div i = 0 ∧ kron_div j = 0) ((I 2) (kron_mod i) (kron_mod j)) 0,
    {
        rw P0_eq_proj_ket0, unfold ket0,
        apply kron_proj_std_basis,
    },
    have r2 : P1 ⊗ X = λ (i j : fin (2*2)), ite (kron_div i = 1 ∧ kron_div j = 1) (X (kron_mod i) (kron_mod j)) 0,
    {
        rw P1_eq_proj_ket1, unfold ket1,
        apply kron_proj_std_basis,
    },
    unfold CNOT,
    rw r1, rw r2,
    unfold X kron_div kron_mod,
    grind_matrix; `[simp],
end

lemma CZ_decompose : CZ = P0 ⊗ (I 2) + P1 ⊗ Z
:= begin
    have r1 : P0 ⊗ (I 2) = λ (i j : fin (2*2)), ite (kron_div i = 0 ∧ kron_div j = 0) ((I 2) (kron_mod i) (kron_mod j)) 0,
    {
        rw P0_eq_proj_ket0, unfold ket0,
        apply kron_proj_std_basis,
    },
    have r2 : P1 ⊗ Z = λ (i j : fin (2*2)), ite (kron_div i = 1 ∧ kron_div j = 1) (Z (kron_mod i) (kron_mod j)) 0,
    {
        rw P1_eq_proj_ket1, unfold ket1,
        apply kron_proj_std_basis,
    },
    unfold CZ,
    rw r1, rw r2,
    unfold Z kron_div kron_mod,
    grind_matrix; `[simp],
end

lemma CZ_decompose_alt : CZ = (I 2) ⊗ P0 + Z ⊗ P1
:= begin
    rw CZ_decompose,

    rw Z_eq_sub_P0_P1,
    rw kron_dist_over_sub_left,
    rw kron_dist_over_sub_right,
    rw add_sub,
    rw add_sub,
    congr' 1,

    rw <- matrix.diagonal_one,
    rw P0_eq_proj_ket0,
    unfold ket0,
    rw proj_std_basis_eq_diagonal,
    rw kron_diagonal,
    rw P1_eq_proj_ket1,
    unfold ket1,
    rw proj_std_basis_eq_diagonal,
    iterate 3 { rw kron_diagonal },
    iterate 2 { rw matrix.diagonal_add },
    congr,
    apply funext, intros i,
    cases i with i ip,
    unfold kron_div kron_mod,
    iterate 4 { cases i, by simp },
    destruct_fin,
end

lemma mul_P0_H : P0 ⬝ H = ![ ![ /√2, /√2 ],
                             ![ 0, 0 ] ]
:= begin
    rw P0_eq_proj_ket0,
    unfold ket0,
    rw mul_proj_std_basis_left,
    unfold H,
    grind_matrix; `[simp],
end

lemma mul_P1_H : P1 ⬝ H = ![ ![ 0, 0 ],
                            ![ /√2, -/√2 ] ]
:= begin
    rw P1_eq_proj_ket1, unfold ket1,
    rw mul_proj_std_basis_left,
    unfold H,
    grind_matrix; `[simp],
end

lemma H_P0_H_eq_P_plus : H ⬝ P0 ⬝ H = P_plus
:= begin
    rw matrix.mul_assoc,
    rw mul_P0_H,
    unfold H P_plus,
    grind_matrix; `[ simp, norm_cast, simp ],
end

lemma H_P1_H_eq_P_minus : H ⬝ P1 ⬝ H = P_minus
:= begin
    rw matrix.mul_assoc,
    rw mul_P1_H,
    unfold H P_minus,
    grind_matrix; `[ simp, norm_cast, simp ],
end

theorem CNOT_eq_H_CZ_H : CNOT = ((I 2) ⊗ H) ⬝ CZ ⬝ ((I 2) ⊗ H)
:= begin
    rw CNOT_decompose,
    rw I_eq_add_P_plus_P_minus,
    rw X_eq_sub_P_plus_P_minus,
    have : P0 ⊗ (P_plus + P_minus) + P1 ⊗ (P_plus - P_minus)
        = (P0 + P1) ⊗ P_plus + (P0 - P1) ⊗ P_minus,
    {
        rw kron_dist_over_add_right,
        rw kron_dist_over_sub_right,
        rw kron_dist_over_add_left,
        rw kron_dist_over_sub_left,
        abel,
    },
    rw this, clear this,
    rw <- I_eq_add_P0_P1,
    rw <- Z_eq_sub_P0_P1,
    have l1: (I 2) ⊗ P_plus = ((I 2) ⊗ H) ⬝ ((I 2) ⊗ P0) ⬝ ((I 2) ⊗ H),
    {
        rw <- H_P0_H_eq_P_plus,
        rw kron_mixed_prod_I_left,
        rw kron_mixed_prod_I_left,
    },
    have l2: Z ⊗ P_minus = ((I 2) ⊗ H) ⬝ (Z ⊗ P1) ⬝ ((I 2) ⊗ H),
    {
        rw <- H_P1_H_eq_P_minus,
        rw kron_mixed_prod_I_left,
        rw kron_mixed_prod_I_right,
    },
    rw l1, clear l1,
    rw l2, clear l2,
    rw <- I_eq_add_P_plus_P_minus,
    rw <- matrix.add_mul,
    congr' 1,
    rw <- matrix.mul_add,
    congr' 1,
    rw CZ_decompose_alt,
end


------------------------------------------------------------------------------
-- Controlled-U gates definitions

lemma CNOT_def : CNOT = controlled_gate X
:= begin
    rw CNOT_decompose,
    unfold controlled_gate,
    rw P0_eq_proj_ket0,
    rw P1_eq_proj_ket1,
end

lemma CZ_def : CZ = controlled_gate Z
:= begin
    rw CZ_decompose,
    unfold controlled_gate,
    rw P0_eq_proj_ket0,
    rw P1_eq_proj_ket1,
end

-- CZ gate's control and target can be swapped and the operater is still the same.
lemma CZ_symmetry : CZ = SWAP ⬝ CZ ⬝ SWAP
:= begin
    unfold CZ SWAP,
    grind_matrix; `[simp],
end

lemma CZ_def' : CZ = gate_controlled Z
:= begin
    unfold gate_controlled,
    rw <- CZ_def,
    apply CZ_eq_upside_down,
end
