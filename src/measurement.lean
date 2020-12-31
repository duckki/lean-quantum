import quantum_lemmas
open Matrix
open quantum
open_locale big_operators

------------------------------------------------------------------------------
-- Generalized measurement

section generalized_measurement

variables {n : ℕ}
variables (M : fin n → Square n) -- a set of measurement operators
variables (s : Vector n) -- state

/-- `Pr(m)` - the probability that we find measurement result `m`.
In other words, measuring the operator `M m` in the state `s`. -/
noncomputable
def gen_measure (m : fin n) : ℝ := ((s† ⬝ ((M m)† ⬝ (M m)) ⬝ s) 0 0).re

/-- The state after general measurement. -/
noncomputable
def state_after_gen_measure (m : fin n) := (1 / real.sqrt (gen_measure M s m)) • M m ⬝ s

end generalized_measurement


section generalized_measurement_lemmas

variables {n : ℕ}
variables {M : fin n → Square n} -- a set of measurement operators
variables {s : Vector n} -- state
variables {m : fin n} -- the index of the measurement operator in the set `M`

lemma gen_measure_eq_inner_product : s† ⬝ ((M m)† ⬝ (M m)) ⬝ s = ((M m) ⬝ s)† ⬝ ((M m) ⬝ s)
:= begin
    rw adjoint_mul,
    iterate 3 { rw matrix.mul_assoc },
end

-- `Pr(m) = ∥M m ⬝ s∥^2`
lemma gen_measure_eq_norm_sq_mul : gen_measure M s m = ∥(M m ⬝ s)∥^2
:= begin
    unfold gen_measure,
    rw gen_measure_eq_inner_product,
    apply Matrix_inner_self_eq_norm_sq,
end

-- `√(Pr(m)) = ∥M m ⬝ s∥`
lemma sqrt_gen_measure_eq_norm_mul : real.sqrt (gen_measure M s m) = ∥(M m ⬝ s)∥
:= begin
    rw gen_measure_eq_norm_sq_mul,
    rw pow_two,
    apply real.sqrt_mul_self,
    apply matrix.norm_nonneg,
end

-- `Pr(m) = Tr(M m ⬝ ρ ⬝ (M m)†)`, where `ρ` is `proj s`.
example (m : fin n) : gen_measure M s m = Tr( M m ⬝ proj s ⬝ (M m)†).re
:= begin
    unfold gen_measure proj,
    congr' 1,
    rw gen_measure_eq_inner_product,
    rw <- trace_outer_eq_inner,
    rw adjoint_mul,
    repeat { rw matrix.mul_assoc },
end

-- `Pr(m) = Tr((M m)† ⬝ M m ⬝ ρ)`, where `ρ` is `proj s`.
example {m : fin n} : gen_measure M s m = Tr( (M m)† ⬝ M m ⬝ proj s).re
:= begin
    unfold gen_measure proj,
    congr' 1,
    rw gen_measure_eq_inner_product,
    rw <- trace_outer_eq_inner,
    rw adjoint_mul,

    have l: M m ⬝ s ⬝ (s† ⬝ M m†) = M m ⬝ (s ⬝ s†) ⬝ (M m)†,
    { repeat { rw matrix.mul_assoc }, },
    rw l, clear l,
    rw trace_mul_rotate_l (M m),
end

lemma state_after_gen_measure_unit {s : Vector n} {m : fin n}
        : gen_measure M s m ≠ 0 → (state_after_gen_measure M s m).unit
:= begin
    intros h,
    rw norm_eq_one_iff_unit,
    unfold state_after_gen_measure,
    rw sqrt_gen_measure_eq_norm_mul, simp,
    rw gen_measure_eq_norm_sq_mul at h,
    have : ∥M m ⬝ s∥ ≠ 0,
    {
        intro c, apply h, clear h,
        rw c, simp,
    },
    exact norm_smul_norm_inv_eq_one this,
end

end generalized_measurement_lemmas


------------------------------------------------------------------------------
-- Projective measurement

section projective_measurement

variables {n : ℕ}
variables (u : fin n → Vector n) -- a set of basis vectors to project
variables (s : Vector n) -- state

/-- `Pr(i)` - the probability that we find measurement result `i` in state `s`.
In other words, measuring the projection of basis `u i` in state `s`. -/
noncomputable
def proj_measure (i : fin n) : ℝ := ((s† ⬝ (proj (u i)) ⬝ s) 0 0).re

/-- The state after projective measurement -/
noncomputable
def state_after_proj_measure (i : fin n)
    := (1 / real.sqrt (proj_measure u s i)) • proj (u i) ⬝ s

end projective_measurement


section projective_measurement_lemmas

variables {n : ℕ}
variables {u : fin n → Vector n} -- a set of basis vectors to project
variables {s : Vector n} -- state

/-- The measurement operator computed from the basis vector `u i` -/
@[reducible] noncomputable
def proj_to_measure (u : fin n → Vector n) (i : fin n) := proj (u i)

/-- All projection vectors in the set `u` are unit. -/
@[reducible]
def proj_unit (u : fin n → Vector n) := ∀ i, (u i).unit

lemma proj_measure_eq_gen_measure_proj
        : proj_unit u
        → proj_measure u = gen_measure (proj_to_measure u)
:= begin
    intros h, ext s m,
    unfold proj_measure gen_measure proj_to_measure,
    rw proj_mul_adjoint_eq_self (h m),
end

variables {i : fin n} -- the index of the projection vector in the set `u`

lemma proj_measure_eq_inner_product : s† ⬝ (proj (u i)) ⬝ s = ((u i)† ⬝ s)† ⬝ ((u i)† ⬝ s)
:= begin
    unfold proj,
    rw adjoint_mul, simp,
    iterate 3 { rw matrix.mul_assoc },
end

-- `Pr(i) = ∥(P i) ⬝ s∥^2`, where `P i` is `proj (u i)`.
-- Inherited property from gen_measure.
lemma proj_measure_eq_norm_sq_mul : proj_unit u → proj_measure u s i = ∥(proj (u i) ⬝ s)∥^2
:= begin
    intro up,
    rw proj_measure_eq_gen_measure_proj up,
    apply gen_measure_eq_norm_sq_mul,
end

-- The Born rule
lemma proj_measure_eq_norm_sq_inner : proj_unit u → proj_measure u s i = ∥((u i)† ⬝ s)∥^2
:= begin
    intro up,
    rw proj_measure_eq_norm_sq_mul up,

    iterate 2 { rw <- Matrix_inner_self_eq_norm_sq },
    unfold proj,
    congr' 1,
    unfold inner inner_product,
    iterate 3 { rw adjoint_mul }, simp,
    have : s† ⬝ (u i ⬝ u i†) ⬝ (u i ⬝ u i† ⬝ s) = s† ⬝ u i ⬝ (u i† ⬝ u i) ⬝ (u i† ⬝ s),
    {
        repeat { rw matrix.mul_assoc },
    },
    rw this, clear this,
    rw unfold_unit (up i), simp,
end

-- Inherited property from gen_measure.
lemma state_after_proj_measure_unit
        : proj_unit u → proj_measure u s i ≠ 0 → (state_after_proj_measure u s i).unit
:= begin
    intros up,
    unfold state_after_proj_measure,
    rw proj_measure_eq_gen_measure_proj up,
    intros h,
    apply state_after_gen_measure_unit h,
end

lemma proj_self_square_of_proj_unit : proj_unit u → (u i).proj ⬝ (u i).proj = (u i).proj
:= begin
    intros up,
    unfold proj,
    have : u i ⬝ u i† ⬝ (u i ⬝ u i†) = u i ⬝ (u i† ⬝ u i) ⬝ u i†,
    { repeat { rw matrix.mul_assoc }, },
    rw this, clear this,
    rw unfold_unit (up i), simp,
end

-- Applying the same (projective) measurement operator has no effect.
lemma proj_measure_state_after_proj_measure
    : proj_unit u
    → (u i).proj ⬝ state_after_proj_measure u s i = state_after_proj_measure u s i
:= begin
    intros up,
    unfold state_after_proj_measure,
    have f: ∀ (s : Square n) (t : Vector n) (a : ℝ), s ⬝ (a • t) = a • (s ⬝ t),
    { intros s t a, apply matrix.mul_smul },
    rw f,
    rw <- matrix.mul_assoc,
    rw proj_self_square_of_proj_unit up,
end

-- The probability of measuring again gives us the same result is 1.
lemma proj_measure_state_after_proj_measure_unit : proj_unit u → proj_measure u s i ≠ 0
        → proj_measure u (state_after_proj_measure u s i) i = 1
:= begin
    intros up h,
    rw proj_measure_eq_norm_sq_mul up,
    rw proj_measure_state_after_proj_measure up,
    have : (state_after_proj_measure u s i).unit,
    { apply state_after_proj_measure_unit; assumption },
    rw <- Matrix_inner_self_eq_norm_sq,
    unfold inner inner_product,
    rw unfold_unit this, simp,
end

end projective_measurement_lemmas


------------------------------------------------------------------------------
-- Standard basis measurement as a projective measurement

section projective_measurement_in_std_basis

variables {n : ℕ} {s : Vector n}

@[simp]
lemma proj_unit_std_basis : @proj_unit n std_basis
:= begin
    unfold proj_unit, intros i, simp,
end

lemma proj_measure_eq_measure
        : proj_measure std_basis s = ⟦s⟧
:= begin
    ext m,
    unfold quantum.measure,
    rw proj_measure_eq_norm_sq_inner,
    {
        rw <- Matrix_inner_self_eq_norm_sq,
        unfold inner inner_product,
        rw matrix_mul_square_one, simp,
    },
    {
        simp,
    }
end

end projective_measurement_in_std_basis


------------------------------------------------------------------------------
-- Simulating projective measurement by measurement in the standard basis

section proj_measure_to_measure

variables {n : ℕ} {s : Vector n}
variables {u : fin n → Vector n} -- a set of basis to project
variables {m : fin n} -- the index of the projection vector in the set `u`

/-- A unitary operator that converts an arbitrary projective measurement to
the standard basis measuremnt. -/
noncomputable
def proj_measure_op (u : fin n → Vector n) : Square n := λ i, (u i)† 0

lemma proj_measure_to_measure : proj_unit u
        → proj_measure u s = ⟦proj_measure_op u ⬝ s⟧
:= begin
    intros h,
    ext m,
    rw <- proj_measure_eq_measure,
    rw proj_measure_eq_norm_sq_inner h,
    rw proj_measure_eq_norm_sq_inner proj_unit_std_basis,
    congr' 2,
    rw <- matrix.mul_assoc,
    congr' 1,

    apply matrix.ext, intros i j,
    have : i = 0, by simp, cases this, clear this,
    simp,
    rw matrix.mul_apply,
    unfold proj_measure_op,
    rw finset.sum_eq_single m; try {solve1 {simp}},
    {
        intros i ip ie,
        rw std_basis_adjoint_apply,
        rw std_basis_eq_zero ie, simp,
    },
end

/-- The unitary operator that restores the state after projective measurement,
after simulating it with `proj_measure_op`. -/
noncomputable
def proj_measure_restore_op (u : fin n → Vector n) (m : fin n) := u m ⬝ (std_basis m)†

lemma state_after_proj_measure_to_measure
        : proj_unit u
        → state_after_proj_measure u s m
            = proj_measure_restore_op u m ⬝ state_after_measure (proj_measure_op u ⬝ s) m
:= begin
    intros up,
    unfold state_after_proj_measure state_after_measure,
    rw proj_measure_to_measure up,
    -- need this since `matrix.mul_smul` is expecting ℂ smul, not ℝ smul.
    have : ∀ (s : Square n) (t : Vector n) (a : ℝ), s ⬝ (a • t) = a • (s ⬝ t),
    { intros s t a, apply matrix.mul_smul },
    rw this, clear this,
    congr' 1,
    unfold proj_measure_op proj_measure_restore_op,
    rw <- matrix.mul_assoc,
    unfold proj,
    have : u m ⬝ std_basis m† ⬝ (std_basis m ⬝ std_basis m†)
         = u m ⬝ std_basis m†,
    {
        rw matrix.mul_assoc,
        rw <- matrix.mul_assoc ((std_basis m)†),
        simp,
    },
    rw this, clear this,
    rw matrix.mul_assoc,
    rw matrix.mul_assoc,
    congr' 1,
    rw <- matrix.mul_assoc,
    congr' 1,
    apply matrix.ext, intros i j,
    have : i = 0, by simp, cases this, clear this, simp,
    rw matrix.mul_apply,
    rw finset.sum_eq_single m; try { solve1 {simp} },
    {
        intros k k_in k_neq,
        simp,
        rw std_basis_eq_zero k_neq,
        left, refl,
    },
end

end proj_measure_to_measure
