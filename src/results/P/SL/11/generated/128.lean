

theorem interior_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior A) ⊆ interior (closure A) := by
  -- Step 1: `interior (interior A)` is contained in `interior (closure (interior A))`.
  have h₁ : interior (interior A) ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  -- Step 2: `interior (closure (interior A))` is contained in `interior (closure A)`.
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Combine the two inclusions.
  exact h₁.trans h₂