

theorem closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- We start with the basic inclusion `interior (closure A) ⊆ closure A`.
  have h : interior (closure A) ⊆ closure A := interior_subset
  -- Applying `closure_mono` to this inclusion yields the desired result.
  simpa [closure_closure] using (closure_mono h)