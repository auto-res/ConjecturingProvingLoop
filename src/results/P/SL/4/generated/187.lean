

theorem interior_eq_empty_of_interior_closure_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure A) = (∅ : Set X) → interior A = (∅ : Set X) := by
  intro h
  ext x
  constructor
  · intro hx
    have hx' : x ∈ interior (closure A) := by
      have h_subset : interior A ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      exact h_subset hx
    simpa [h] using hx'
  · intro hx
    cases hx