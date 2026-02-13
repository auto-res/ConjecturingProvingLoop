

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ interior A = A := by
  -- First, rewrite `P3 A` in terms of an inclusion using the previous lemma.
  have h₁ : P3 A ↔ (A ⊆ interior A) := P3_closed_iff (A := A) hA
  -- For a closed set, this inclusion is equivalent to equality.
  have h₂ : (A ⊆ interior A) ↔ interior A = (A : Set X) := by
    constructor
    · intro hsub
      exact Set.Subset.antisymm interior_subset hsub
    · intro h_eq
      simpa [h_eq] using
        (subset_rfl : (interior A : Set X) ⊆ interior A)
  -- Combine the two equivalences.
  simpa using h₁.trans h₂