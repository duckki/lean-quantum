import quantum_lemmas

open Matrix

local notation `|0^(` n `)⟩` := ket_zeros n

------------------------------------------------------------------------------
-- no-clone theorem (with 1 input qubit and 1 ancilla qubit)

section no_clone_1

-- Note: lean can't detect contradiction from `/√2 = 1/2`. Convert it to reals.
lemma no_clone_contra_h : /√2 = 1/2 → false
:= begin
    intros h,
    let c1 := eq_of_one_div_eq_one_div h,
    norm_cast at c1,
    have c2: (2 : ℝ) = 4, {
        calc 2 = √2 * √2 : by {rw real.mul_self_sqrt, linarith}
           ... = 2 * 2 : by rw c1
           ... = (4 : ℝ) : by linarith,
    },
    linarith,
end

lemma no_clone_contra : ¬ (∀ (x y : Vector 2), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y))
:= begin
    intros h,
    have f1: (|0⟩† ⬝ |+⟩) = λ _ _, /√2, {
        unfold_qubits; grind_matrix, grind_dot_product; finish_complex_arith,
    },
    have f2: (|0⟩† ⬝ |+⟩) = λ _ _, 1/2, {
        rw h,
        rw f1,
        unfold kron,
        apply funext, intro i,
        apply funext, intro j,
        norm_cast,
        rw div_mul_div,
        rw real.mul_self_sqrt,
        norm_cast, simp,
        linarith,
    },
    have f1': (|0⟩† ⬝ |+⟩) 0 0 = /√2, {
        rw f1,
    },
    have f2': (|0⟩† ⬝ |+⟩) 0 0 = 1/2, {
        rw f2,
    },
    have c: /√2 = 1/2, {
        rw <- f1',
        rw <- f2',
    },
    apply no_clone_contra_h c,
end

theorem no_clone_1
    : ¬ (∃ (U : Matrix 4 4), U.unitary ∧ ∀ s : Vector 2, U ⬝ (s ⊗ |0⟩) = s ⊗ s)
:= begin
    intros h, rcases h with ⟨U, ⟨H1, H2⟩⟩,

    -- Part 1: derive the main contradictory fact.
    have f1: ∀ (x y : Vector 2), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y), {
        intros x y,
        have g1: (x† ⊗ (|0⟩†)) ⬝ (U† ⬝ U) ⬝ (y ⊗ |0⟩) = (x† ⊗ (x†)) ⬝ (y ⊗ y), {
            rw <- matrix.mul_assoc,
            rw <- adjoint_kron,
            rw <- adjoint_mul,
            rw H2,
            rw matrix.mul_assoc,
            rw H2,
            congr' 1,
            rw <- adjoint_kron,
        },
        calc (x†) ⬝ y = (x† ⬝ y) ⊗ (|0⟩† ⬝ |0⟩) : by simp
                  ... = (x† ⊗ (|0⟩†)) ⬝ (y ⊗ |0⟩) : by rw kron_mixed_prod
                  ... = (x† ⊗ (|0⟩†)) ⬝ (U† ⬝ U) ⬝ (y ⊗ |0⟩) : by {rw unfold_unitary H1, simp}
                  ... = (x† ⊗ (x†)) ⬝ (y ⊗ y) : g1
                  ... = (x† ⬝ y) ⊗ (x† ⬝ y) : by rw kron_mixed_prod,
    },

    -- Part 2:  derive false from the `f1`.
    apply no_clone_contra f1,
end

end no_clone_1


------------------------------------------------------------------------------
-- no-clone theorem 2 (with n input qubit and n ancilla qubit)
-- Similar to no_clone_1, but generalized with n qubits.

section no_clone_2

-- Note: The vector size needs to have this formula: (2 * 2^n) to make it easier to match.
lemma no_clone_contra_2 (n : ℕ) : ¬ (∀ (x y : Vector 2 * (2^n)), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y))
:= begin
    intros h,
    have f1: ((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩) = λ _ _, /√2, {
        rw adjoint_kron,
        rw kron_mixed_prod,
        simp,
        unfold_qubits; grind_matrix, grind_dot_product; finish_complex_arith,
    },
    have f2: ((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩) = λ _ _, 1/2, {
        rw h,
        rw f1,
        unfold kron,
        apply funext, intro i,
        apply funext, intro j,
        norm_cast,
        rw div_mul_div,
        rw real.mul_self_sqrt,
        norm_cast, simp,
        linarith,
    },

    let fin0 := (⟨0, by simp⟩ : fin (1*1)),
    have f1': (((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩)) fin0 fin0 = /√2, {
        rw f1,
    },
    have f2': (((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩)) fin0 fin0 = 1/2, {
        rw f2,
    },
    have c: /√2 = 1/2, {
        rw <- f1',
        rw <- f2',
    },
    apply no_clone_contra_h c,
end

theorem no_clone_2 (n : ℕ) (npos : 0 < n)
    : ¬ (∃ (U : Square (2^n * 2^n))
         , U.unitary ∧ ∀ (s : Vector 2^n), U ⬝ (s ⊗ |0^(n)⟩) = s ⊗ s)
:= begin
    intros h, rcases h with ⟨U, ⟨H1, H2⟩⟩,

    -- Part 1: derive the main contradictory fact.
    have f1: ∀ (x y : Vector 2^n), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y), {
        intros x y,
        have g1: (x† ⊗ (|0^(n)⟩†)) ⬝ (U† ⬝ U) ⬝ (y ⊗ |0^(n)⟩) = (x† ⊗ (x†)) ⬝ (y ⊗ y), {
            rw <- matrix.mul_assoc,
            rw <- adjoint_kron,
            rw <- adjoint_mul,
            rw H2,
            rw matrix.mul_assoc,
            rw H2,
            congr' 1,
            rw <- adjoint_kron,
        },
        calc (x†) ⬝ y = (x† ⬝ y) ⊗ (|0^(n)⟩† ⬝ |0^(n)⟩) : by simp
                  ... = (x† ⊗ (|0^(n)⟩†)) ⬝ (y ⊗ |0^(n)⟩) : by rw kron_mixed_prod
                  ... = (x† ⊗ (|0^(n)⟩†)) ⬝ (U† ⬝ U) ⬝ (y ⊗ |0^(n)⟩) : by {rw unfold_unitary H1, simp}
                  ... = (x† ⊗ (x†)) ⬝ (y ⊗ y) : g1
                  ... = (x† ⬝ y) ⊗ (x† ⬝ y) : by rw kron_mixed_prod,
    },

    -- Part 2:  derive false from the `f1`.
    cases n, {
        exfalso, linarith,
    }, {
        apply no_clone_contra_2 _ f1,
    },
end

end no_clone_2


------------------------------------------------------------------------------
-- no-clone theorem 3 (with 1 input qubit and (n+1) ancilla qubits)

section no_clone_3_helpers

variables {n : ℕ}
variables {U : Square (2 ^ (n + 2))} {f : (Vector 2) → Vector (2^n)}

-- Any `f x` must be unit, since `U` is a unitary operator.
lemma no_clone_3_unit {x : Vector 2} :
    (∀ s : Vector 2, s.unit → U ⬝ (s ⊗ (|0^(n+1)⟩)) = (s ⊗ (s ⊗ (f s))))
    → U.unitary → x.unit
    → (f x).unit
:= begin
    intros h u xu,
    have f1: (x ⊗ (x ⊗ f x)).unit, {
        rw <- h _ xu,
        unfold matrix.unit,
        rw unitary_preserve_norm _ _ _ u,
        change ((x ⊗ |0^(n + 1)⟩).unit),
        apply unit_kron_of_unit; try {simp *},
        unfold matrix.unit ket_zeros, simp,
    },
    apply unit_kron_right,
    apply unit_kron_right f1; assumption,
    assumption,
end

-- The contradictory formula
lemma no_clone_3_contradiction {x y : Vector 2} :
    (∀ s : Vector 2, s.unit → U ⬝ (s ⊗ (|0^(n+1)⟩)) = (s ⊗ (s ⊗ (f s))))
    → U.unitary → x.unit → y.unit
    → (x†) ⬝ y ≠ 0
    → (x† ⬝ y) ⬝ ((f x)† ⬝ f y) = 1
:= begin
    intros h u xu yu h',

    have fx1: x ⊗ (x ⊗ (f x)) = U ⬝ (x ⊗ (|0^(n+1)⟩)), by rw h; assumption,
    have fy1: y ⊗ (y ⊗ (f y)) = U ⬝ (y ⊗ (|0^(n+1)⟩)), by rw h; assumption,

    have f1: ((x ⊗ (x ⊗ (f x)))†) ⬝ (y ⊗ (y ⊗ (f y))) = ((x ⊗ (|0^(n+1)⟩))†) ⬝ (y ⊗ (|0^(n+1)⟩)), {
        rw fx1, rw fy1,
        rw unitary_preserve_norm; assumption,
    },

    repeat { rw adjoint_kron at f1 },
    repeat { rw kron_mixed_prod at f1 },
    unfold ket_zeros at f1, simp at f1,
    repeat { rw kron_one_by_one_eq_mul at f1 },
    repeat { rw kron_square_one_eq_mul at f1 },

    have f2: ((x†) ⬝ y) ⬝ (x† ⬝ y ⬝ (f x† ⬝ f y)) = (x† ⬝ y) ⬝ 1, {
        simp, assumption,
    },

    apply matrix_mul_cancel_left_square_one f2; assumption,
end

end no_clone_3_helpers

theorem no_clone_3 {n}
    : ¬ (∃ (U : Square (2 ^ (n + 2))) (f : (Vector 2) → Vector (2^n))
         , U.unitary
         ∧ (∀ s : Vector 2, s.unit → U ⬝ (s ⊗ (|0^(n+1)⟩)) = (s ⊗ (s ⊗ (f s)))))
:= begin
    by_contradiction H,
    rcases H with ⟨U, ⟨f, H⟩⟩,
    rcases H with ⟨u, h⟩,

    -- Step 1. Derive facts about "f" based on the fact that
    --         U is a unitary operatros.
    have f_ket0_unit: (f |0⟩).unit, {
        apply no_clone_3_unit h u; try {solve1 {simp *}},
    },
    have f_ket_plus_unit: (f |+⟩).unit, {
        apply no_clone_3_unit h u; try {solve1 {simp *}},
    },
    have f1: |⟪ f |0⟩, f |+⟩ ⟫| ≤ 1, {
        apply inner_product_bound_of_unit; assumption,
    },

    -- Step 2. Derive the contradictory fact from the expected result state.
    have c1: (|0⟩† ⬝ |+⟩) ⬝ ((f |0⟩)† ⬝ f |+⟩) = 1, {
        apply no_clone_3_contradiction h; simp <|> assumption,
        rw inner_product_zero_iff, rw inner_ket0_ket_plus, simp,
    },

    -- Step 3, combine Step #1 and #3 to deduce "false".
    have c2: ⟪ f |0⟩, f |+⟩ ⟫ = √2, {
        have c1': ⟪ |0⟩, |+⟩ ⟫ * ⟪ f |0⟩, f |+⟩ ⟫ = 1, {
            rw <- matrix.ext_iff at c1, specialize c1 0 0,
            rw matrix_mul_square_one at c1, simp at c1,
            apply c1,
        },
        rw inner_ket0_ket_plus at c1',
        have c2_1: (√2 * (/√2 * ⟪ f |0⟩, f |+⟩ ⟫) : ℂ) = √2 * 1, {
            rw c1',
        },
        calc ⟪ f |0⟩, f |+⟩ ⟫ = √2 * (/√2 * ⟪ f |0⟩, f |+⟩ ⟫) : by {simp,}
                         ... = √2 : by {rw c2_1, simp,},
    },
    have c3: |(√2 : ℂ)| ≤ 1 → false, {
        simp, rw _root_.abs_of_nonneg, {
            contrapose!, intro h, clear h, simp,
        }, {
            simp,
        }
    },
    apply c3,
    rw <- c2, assumption,
end


------------------------------------------------------------------------------
-- no-clone theorem 3 (with 1 input qubit and (n+1) ancilla qubits)
-- Alternative proof based on partial measure.

lemma no_clone_3_alt_helper1 (i : fin 4) : (/√2 • (|0⟩ ⊗ |0⟩) i 0)† * (/√2 • (|1⟩ ⊗ |1⟩)) i 0 = 0
:= begin
    unfold_qubits,
    unfold kron kron_div kron_mod,
    repeat { destruct_fin }; simp,
end

lemma no_clone_3_alt_helper2 : ⟦(|+⟩ ⊗ |+⟩)⟧ 1 = 1/4
:= begin
    unfold quantum.measure,
    unfold_qubits,
    unfold kron kron_div kron_mod,
    repeat { destruct_fin }; simp; ring,
end

lemma no_clone_3_alt_helper3 : ⟦(/√2 • (|0⟩ ⊗ |0⟩)) + (/√2 • (|1⟩ ⊗ |1⟩))⟧ 1 = 0
:= begin
    unfold quantum.measure,
    unfold_qubits,
    unfold kron kron_div kron_mod,
    repeat { destruct_fin }; simp,
end

theorem no_clone_3_alt {n}
    : ¬ (∃ (U : Square (2 ^ (n + 2))) (f : (Vector 2) → Vector (2^n))
         , U.unitary
         ∧ (∀ s : Vector 2, s.unit → U ⬝ (s ⊗ (|0^(n+1)⟩)) = (s ⊗ (s ⊗ (f s)))))
:= begin
    by_contradiction H,
    rcases H with ⟨U, ⟨f, H⟩⟩,
    rcases H with ⟨u, H⟩,

    let U_0 := (H (|0⟩)),
    let U_1 := (H (|1⟩)),
    let U_plus := (H |+⟩),

    -- Step 1. Compute the state after cloning |+⟩
    have step1 : U ⬝ (|+⟩ ⊗ |0^(n+1)⟩) = /√2 • U ⬝ (|0⟩ ⊗ |0^(n+1)⟩)
                                      + /√2 • U ⬝ (|1⟩ ⊗ |0^(n+1)⟩), {
        iterate 2 { rw <- matrix.mul_smul },
        iterate 2 { rw <- kron_smul_left },
        rw <- matrix.mul_add,
        congr' 1,
        rw <- kron_dist_over_add_left,
        congr' 1,
        rw ket_plus_alt_def,
    },

    -- Step 2. Compute the state after cloning |0⟩ or |1⟩ with a 50% probability.
    --         This should be identical to the Step #1 when combined.
    have step2_1: /√2 • U ⬝ (|0⟩ ⊗ |0^(n+1)⟩) = /√2 • |0⟩ ⊗ (|0⟩ ⊗ f |0⟩), {
        congr' 1, apply H, simp,
    },
    have step2_2: /√2 • U ⬝ (|1⟩ ⊗ |0^(n+1)⟩) = /√2 • |1⟩ ⊗ (|1⟩ ⊗ f |1⟩), {
        congr' 1, apply H, simp,
    },

    -- Step 3. Equate the results of Step #1 and #2, which will be contradictory.
    have step3: |+⟩ ⊗ (|+⟩ ⊗ f |+⟩) = (/√2 • |0⟩ ⊗ (|0⟩ ⊗ f |0⟩)) + (/√2 • |1⟩ ⊗ (|1⟩ ⊗ f |1⟩)), {
        rw <- U_plus; try {solve1 {simp}},
        rw step1,
        rw <- step2_1,
        rw <- step2_2,
    },

    -- Step 4. Reformulate the equation from Step #3, before making a partial measurement.
    have step4: (|+⟩ ⊗ |+⟩) ⊗ f |+⟩ = (/√2 • (|0⟩ ⊗ |0⟩)) ⊗ f |0⟩ + (/√2 • (|1⟩ ⊗ |1⟩)) ⊗ f |1⟩, {
        rw kron_assoc_l2r,
        rw step3,
        simp,
        repeat { rw kron_assoc },
        rw push_cast_matrix_add; try {ring},
        iterate 2 { rw push_cast_matrix_smul; try {ring} },
        iterate 2 { rw cast_roundtrip },
    },
    clear step1 step2_1 step2_2 step3 U_plus U_0 U_1,

    -- Step 5. Derive facts about "f" based on the fact that
    --         U is a unitary operatros.
    have f_ket0_unit: (f |0⟩).unit, {
        apply no_clone_3_unit H u; try {solve1 {simp *}},
    },
    have f_ket1_unit: (f |1⟩).unit, {
        apply no_clone_3_unit H u; try {solve1 {simp *}},
    },
    have f_ket_plus_unit: (f |+⟩).unit, {
        apply no_clone_3_unit H u; try {solve1 {simp *}},
    },

    -- Step 6. Find contradiction form the partial measurements of both sides.
    have c1: ⟦(|+⟩ ⊗ |+⟩)⟧ 1 = ⟦(/√2 • (|0⟩ ⊗ |0⟩)) + (/√2 • (|1⟩ ⊗ |1⟩))⟧ 1, {
        have p1: ⦃ (|+⟩ ⊗ |+⟩) ⊗ f |+⟩ ⦄ = ⟦(|+⟩ ⊗ |+⟩)⟧, {
            apply partial_measure_proj_kron,
            apply trace_proj_eq_one_of_unit; assumption,
        },
        have p2: ⦃ (/√2 • (|0⟩ ⊗ |0⟩)) ⊗ f |0⟩ + (/√2 • (|1⟩ ⊗ |1⟩)) ⊗ f |1⟩ ⦄
                = ⟦ (/√2 • (|0⟩ ⊗ |0⟩)) + (/√2 • (|1⟩ ⊗ |1⟩)) ⟧, {
            apply partial_measure_add_kron_of_orthogonal,
            apply trace_proj_eq_one_of_unit; assumption,
            apply trace_proj_eq_one_of_unit; assumption, {
                apply no_clone_3_alt_helper1,
            },
        },
        rw <- p1,
        rw <- p2,
        rw step4,
    },
    have c2: (1/4 : ℝ) = 0, {
        rw <- no_clone_3_alt_helper2,
        rw <- no_clone_3_alt_helper3,
        apply c1,
    },
    norm_num at c2,
end
