import data.complex.is_R_or_C
import data.matrix.basic
import common_lemmas

------------------------------------------------------------------------------
-- Convenience definition for complex numbers

notation |x| := is_R_or_C.abs x
notation x `†`:90 := @is_R_or_C.conj ℂ _ x

------------------------------------------------------------------------------
-- Convenience definitions for complex matrix

@[reducible]
def Matrix (m n : ℕ) := matrix (fin m) (fin n) ℂ

namespace Matrix

variables {m n : ℕ}

noncomputable
def adjoint (M : Matrix m n) : Matrix n m
| x y := (M y x)†

end Matrix

notation `Vector` n := Matrix n 1
notation `Square` n := Matrix n n
notation `I` n := (1 : Matrix n n)

infixl ` ⬝ ` := matrix.mul
postfix `†`:100 := Matrix.adjoint


------------------------------------------------------------------------------
-- Vector properties

namespace matrix

variables {n : ℕ} (s : Vector n)

-- The property of "unit" Vectors.
def unit := s† ⬝ s = 1

end matrix


------------------------------------------------------------------------------
-- Square matrix properties

namespace Matrix

variables {n : ℕ} (M : Square n)

def normal := (M†) ⬝ M = M ⬝ (M†)

def unitary := (M†) ⬝ M = 1

end Matrix


------------------------------------------------------------------------------
-- Standard basis `std_basis` for a column vector with a single value
-- Note: There is matrix.std_basis_matrix in mathlib. But, I have a difficulty
--       using Matrix with it, partially because it uses `unit` type, instead
--       of `fin 1`.

section std_basis

variables {m : Type*} [fintype m]
variables [decidable_eq m]

-- Note: This definition is not computable (depends on complex.field).
--def std_basis (i : m) : matrix m (fin 1) ℂ := matrix.std_basis_matrix i 0 1

-- column vector with a single value at a given row
def std_basis (i : m) : matrix m (fin 1) ℂ
:= λ j _, if j = i then 1 else 0

end std_basis


------------------------------------------------------------------------------
-- Kronecker product definition

section kron

variables {m n p q : ℕ}

-- kron_div: `i / p` : `fin m`
@[reducible]
def kron_div (i : fin (m*p)) : fin m :=
⟨ (i : ℕ)/p, (nat.div_lt_iff_lt_mul (i : ℕ) m (fin_mul_right_has_zero i)).mpr i.property⟩

-- kron_mod: `i % p` : `fin p`
@[reducible]
def kron_mod (i : fin (m*p)) : fin p :=
⟨ (i : ℕ)%p, nat.mod_lt (i : ℕ) (fin_mul_right_has_zero i) ⟩

-- Kronecker product
def kron (A : Matrix m n) (B : Matrix p q) : Matrix (m*p) (n*q)
:= λ i j,   -- A (i/p) (j/q) * B (i%p) (j%q)
      A (kron_div i) (kron_div j)
    * B (kron_mod i) (kron_mod j)

-- kron_loc: `m * r + v : fin (m * p)
-- Reverses `(r, v)` back to `x`, where `r = kron_div x` and `v = kron_mod x`.
@[reducible]
def kron_loc (r : fin m) (v : fin p) : fin (m * p) :=
⟨ p * (r : ℕ) + (v : ℕ), fin_add_mul_lt r v⟩

end kron

infixl ` ⊗ `:75 := kron  -- same as ` ⬝ ` for now
