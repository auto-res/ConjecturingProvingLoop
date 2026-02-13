

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `closure (interior A)` is contained in `closure A`,
  -- because `interior A ⊆ A` and `closure` is monotone.
  have hsubset : closure (interior A) ⊆ closure A := by
    exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Applying monotonicity of `interior` to the previous inclusion
  -- yields the desired result.
  exact interior_mono hsubset