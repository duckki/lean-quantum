import data.nat.basic
import data.fin

import tactic.linarith

open fin

---------------------------------------------------------------------------------------------
-- nat lemmas

lemma nat_add_mul_left_div_left {a b : ℕ} {c : ℕ} (c_pos : 0 < c) : (c * a + b) / c = a + b/c
:= begin
    rw add_comm,
    rw nat.add_mul_div_left _ _ c_pos,
    ring,
end

lemma nat_add_mul_left_mod_left {a b : ℕ} {c : ℕ} : (c * a + b) % c = b%c
:= begin
    rw add_comm,
    rw nat.add_mul_mod_self_left,
end

lemma add_mul_congr_factor_lt_contra {a b c d e : ℕ}
    : c < a → b < d → ¬ a * b + c = a * d + e
:= begin
    intros cp ep h,
    have h3: a * b + c < a * (b + 1), {
        apply add_lt_add_left; linarith,
    },
    have h4: a * (b + 1) ≤ a * d, {
        apply mul_le_mul; linarith,
    },
    linarith,
end

lemma add_mul_congr_factor {a b c d e : ℕ}
    : c < a → e < a → a * b + c = a * d + e → b = d
:= begin
    intros cp ep h,
    by_contradiction h1,
    cases (ne.lt_or_lt h1) with h2 h2, {
        apply add_mul_congr_factor_lt_contra cp h2 h,
    }, {
        apply add_mul_congr_factor_lt_contra ep h2 (eq.symm h),
    }
end

lemma add_mul_congr {a b c d e : ℕ}
    : a * b + c = a * d + e → c < a → e < a → b = d ∧ c = e
:= begin
    intros h cp ep,
    cases (add_mul_congr_factor cp ep h),
    split, {
        refl,
    }, {
        rw add_right_inj at h,
        exact h,
    }
end


------------------------------------------------------------------------------
-- nat.mod lemmas

section nat_mod

variables (n : ℕ) {m : ℕ}

lemma nat_decomposable_mul_add : 0 < m → ∃ r s, s < m ∧ n = m * r + s
:= begin
    intros mh,
    induction n, {
        use 0,
        use 0,
        split,
        assumption,
        simp,
    }, {
        rcases n_ih with ⟨r', ⟨s', ⟨h1, h2⟩⟩⟩,

        by_cases c: s' + 1 < m, {
            use r',
            use (s' + 1),
            split, {
                assumption,
            }, {
                rw h2,
                rw <- nat.add_one,
                ring,
            }
        }, {
            have c': m = s' + 1, {
                linarith,
            },
            use (r' + 1),
            use (s' + 1 - m),
            rw c',
            split, {
                linarith,
            }, {
                simp,
                rw h2,
                rw <- nat.add_one,
                rw c',
                ring,
            }
        }
    }
end

lemma nat_decompose_mul_add : 0 < m → n = m * (n / m) + (n % m)
:= begin
    intros mh,
    rcases (nat_decomposable_mul_add n mh) with ⟨r, ⟨s, ⟨h1,h2⟩⟩⟩,
    apply eq.trans h2,
    congr, {
        rw h2,
        rw add_comm,
        rw nat.add_mul_div_left; try {assumption},
        rw nat.div_eq_of_lt; assumption <|> simp,
    }, {
        rw h2,
        rw nat.add_mod, simp,
        rw nat.mod_eq_of_lt h1,
    }
end

end nat_mod


------------------------------------------------------------------------------
-- fin coe simplication lemmas

@[simp]
lemma fin_coe_coe_nat_eq_self (n : ℕ) : ((n : fin n.succ) : ℕ) = n
:= begin
    rw coe_eq_val,
    rw coe_val_of_lt, simp,
end


------------------------------------------------------------------------------
-- fin lemmas

lemma fin_has_zero {n} (i : fin n) : 0 < n
:= begin
    cases i,
    linarith,
end

lemma fin_mul_left_has_zero {m p} (i : fin (m*p)) : 0 < m
:= begin
    have f1: 0 < m * p, {
        apply fin_has_zero i,
    },
    apply pos_of_mul_pos_right f1; simp,
end

lemma fin_mul_right_has_zero {m p} (i : fin (m*p)) : 0 < p
:= begin
    have f1: 0 < m * p, {
        apply fin_has_zero i,
    },
    apply pos_of_mul_pos_left f1; simp,
end

lemma fin_add_mul_lt {m p : ℕ} (r : fin m) (v : fin p) : p * (r : ℕ) + (v : ℕ) < m * p
:= begin
    cases r with r hr,
    cases v with v hv,
    simp,
    have f1: p * (r + 1) ≤ p * m, {
        apply mul_le_mul; linarith,
    },
    calc p * r + v < p * r + p : by linarith
               ... = p * (r + 1) : by ring
               ... ≤ p * m : f1
               ... = m * p : by ring,
end


------------------------------------------------------------------------------
-- `cast` reduction: `fin n` cast to `fin n'` coe'd to `ℕ`.

lemma coe_cast_fin_h {n n'} (h : n = n') (i : fin n)
    : (((cast (congr_arg fin h) (i : fin n)) : fin n') : ℕ) = (i : fin n)
:= begin
    congr; assumption <|> apply h.symm <|> skip,
    exact cast_heq (congr_arg fin h) i,
end

lemma coe_cast_fin {n n'} (h : n = n') (i : fin n)
    : (((cast (congr_arg fin h) (i : fin n)) : fin n') : ℕ) = i
:= begin
    rw coe_cast_fin_h; simp,
end


------------------------------------------------------------------------------------------------
-- `cast` helpers

section cast

variables {A B : Type}
variables {a : A}
variables {b : B}

lemma cast_roundtrip (H1 : A = B) : cast H1.symm (cast H1 a) = a
:= begin
    cases H1,
    refl,
end

lemma cast_eq_of_heq (H1: A = B) : a == b → cast H1 a = b
:= begin
    intros h,
    cases h,
    refl,
end

end cast

section fun_cast

variables {A1 A2 R : Type}
variables (f : A1 → R)

lemma congr_heq_arg {x' : A2} {x : A1} (h : x' == x) : (A1 → R) = (A2 → R)
:= begin
    cases h, cc,
end

lemma cast_fun_apply_eq_of_heq_arg (x' : A2) (x : A1) (h : x' == x) : cast (congr_heq_arg h) f x' = f x
:= begin
    cases h; refl,
end

theorem cast_apply (h : A1 = A2) (x' : A2) : cast (congr_arg _ h) f x' = f (cast h.symm x')
:= begin
    rw cast_fun_apply_eq_of_heq_arg,
    apply heq_of_eq_mp; refl,
end

variables {B1 B2 : Type}
variables (f2 : A1 → B1 → R)

lemma congr_heq_arg2 {x' : A2} {y' : B2} {x : A1} {y : B1} (h1 : x' == x) (h2 : y' == y)
        : (A1 → B1 → R) = (A2 → B2 → R)
:= begin
    cases h1, cases h2, cc,
end

lemma cast_fun_apply_eq_of_heq_arg2 (x1 : A2) (x2 : B2) (y1 : A1) (y2 : B1) (h1 : x1 == y1) (h2 : x2 == y2)
        : cast (congr_heq_arg2 h1 h2) f2 x1 x2 = f2 y1 y2
:= begin
    cases h1, cases h2, refl,
end

theorem cast_apply2 (ha : A1 = A2) (hb : B1 = B2) (x : A2) (y : B2)
            : cast (congr_arg2 _ ha hb) f2 x y = f2 (cast ha.symm x) (cast hb.symm y)
:= begin
    rw cast_fun_apply_eq_of_heq_arg2; apply heq_of_eq_mp; refl,
end

end fun_cast
