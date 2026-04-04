import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

open BigOperators

namespace EncodedMatMul

universe u

/--
A pairing abstraction. We avoid committing to Cantor pairing at first.
All we need is an encoding from index pairs to a single type `α`.
-/
structure Pairing (α : Type u) where
  pair : Nat → Nat → α
  unpair : α → Nat × Nat
  left_inv : ∀ i j, unpair (pair i j) = (i, j)

variable {α : Type u} (P : Pairing α)

/--
A matrix encoded as a single-argument function.
Outside the declared shape it is zero.
We use 1-based indexing at the paper level, but Lean is cleaner with 0-based finite indices.
So `m × n` means row indices `0, ..., m-1` and column indices `0, ..., n-1`.
-/
def encMatrix (m n : Nat) (A : Fin m → Fin n → ℝ) : α → ℝ :=
  fun t =>
    let (i, j) := P.unpair t
    if hi : i < m then
      if hj : j < n then
        A ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

/--
Encoded matrix multiplication.
-/
def encMul (m n p : Nat)
    (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin p → ℝ) : α → ℝ :=
  fun t =>
    let (i, j) := P.unpair t
    if hi : i < m then
      if hj : j < p then
        ∑ k : Fin n, A ⟨i, hi⟩ k * B k ⟨j, hj⟩
      else 0
    else 0

def matMul {m n p : Nat}
    (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin p → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/--
The encoded product evaluated at an encoded valid index is the expected finite sum.
This is the first theorem to nail down.
-/
theorem encMul_pair_eq_sum
    {m n p : Nat}
    (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin p → ℝ)
    (i : Fin m) (j : Fin p) :
    encMul P m n p A B (P.pair i.1 j.1)
      = ∑ k : Fin n, A i k * B k j := by
  unfold encMul
  rw [P.left_inv i.1 j.1]
  simp [i.2, j.2]

/--
The encoded matrix agrees with the original matrix on valid encoded indices.
-/
theorem encMatrix_pair_eq
    {m n : Nat}
    (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    encMatrix P m n A (P.pair i.1 j.1) = A i j := by
  unfold encMatrix
  rw [P.left_inv i.1 j.1]
  simp [i.2, j.2]

/--
If the decoded index is outside bounds, the encoded matrix is zero.
Useful later for "total function" behavior.
-/
theorem encMatrix_zero_of_row_ge
    {m n : Nat}
    (A : Fin m → Fin n → ℝ)
    {t : α}
    (h : m ≤ (P.unpair t).1) :
    encMatrix P m n A t = 0 := by
  unfold encMatrix
  simp [Nat.not_lt_of_ge h]

theorem encMatrix_zero_of_col_ge
    {m n : Nat}
    (A : Fin m → Fin n → ℝ)
    {t : α}
    (hrow : (P.unpair t).1 < m)
    (hcol : n ≤ (P.unpair t).2) :
    encMatrix P m n A t = 0 := by
  unfold encMatrix
  simp [hrow, Nat.not_lt_of_ge hcol]

theorem encMul_eq_encMatrix_matMul
    {m n p : Nat}
    (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin p → ℝ)
    (i : Fin m) (j : Fin p) :
    encMul P m n p A B (P.pair i.1 j.1)
      = encMatrix P m p (matMul A B) (P.pair i.1 j.1) := by
  rw [encMul_pair_eq_sum (P := P) A B i j]
  rw [encMatrix_pair_eq (P := P) (A := matMul A B) i j]
  rfl

end EncodedMatMul
