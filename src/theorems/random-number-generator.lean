import quantum_lemmas

open Matrix

------------------------------------------------------------------------------
-- Single qubit random number generator circuit

meta def solve_rng :=
    `[  intros,
        unfold quantum.measure,
        unfold_qubits,
        simp,
        try { unfold H },
        grind_dot_product; `[try {solve1 {simp <|> dec_trivial}}],
        repeat {destruct_fin; `[try {simp}; try {solve1 {ring}}]}]

-- Simply apply `H` gate to `|0⟩`. The result state has the same probability
-- measured in any standard basis.
example : ∀ i, ⟦H ⬝ |0⟩⟧ i = 1/2 := by solve_rng

-- Same result when `|1⟩` is used as the input state.
example : ∀ i, ⟦H ⬝ |1⟩⟧ i = 1/2 := by solve_rng


------------------------------------------------------------------------------
-- Proof automation lemmas
-- These ground facts were needed to simplify `H2 ⬝ |00⟩` evaluations.

@[simp] lemma fin_one_succ_succ_div_2 : (⟨(1 : ℕ).succ.succ / 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_num
@[simp] lemma fin_one_succ_succ_mod_2 : (⟨(1 : ℕ).succ.succ % 2, by dec_trivial⟩ : fin 2) = ⟨1, by dec_trivial⟩ := by norm_num


------------------------------------------------------------------------------
-- 2 qubit random number generator circuit

-- 2-qubit H circut
noncomputable
def H2 : Square 4 := H ⊗ H

meta def solve_rng2 :=
    `[  intros,
        unfold quantum.measure,
        unfold_qubits,
        simp,
        try { unfold H2 },
        try { unfold H },
        try { unfold kron kron_div kron_mod },
        grind_dot_product; `[try {solve1 {simp <|> dec_trivial}}],
        repeat {destruct_fin; `[try {simp}; try {solve1 {ring}}]}]

-- H2 is a 2-qubit random number generator. The input qubits can be either 0/1 individually.
example : ∀ (i : fin 4), ⟦H2 ⬝ |00⟩⟧ i = 1/4 := by solve_rng2
example : ∀ (i : fin 4), ⟦H2 ⬝ |01⟩⟧ i = 1/4 := by solve_rng2
example : ∀ (i : fin 4), ⟦H2 ⬝ |10⟩⟧ i = 1/4 := by solve_rng2
example : ∀ (i : fin 4), ⟦H2 ⬝ |11⟩⟧ i = 1/4 := by solve_rng2
