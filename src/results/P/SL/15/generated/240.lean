

theorem denseInterior_implies_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior A) → closure A = (Set.univ : Set X) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have h_closureInt : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Since `interior A ⊆ A`, we have `closure (interior A) ⊆ closure A`.
  have h_subset : (Set.univ : Set X) ⊆ closure A := by
    have : (closure (interior A : Set X)) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [h_closureInt] using this
  -- Combine the two inclusions to obtain the desired equality.
  apply Set.Subset.antisymm
  · intro _ _; trivial
  · exact h_subset