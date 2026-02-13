

theorem closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- The interior of `A` is contained in `A`.
  have hInt : interior (A : Set X) ⊆ (A : Set X) := interior_subset
  -- Taking closures preserves inclusions.
  have hCl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono hInt
  -- Since `A` is closed, its closure equals itself.
  simpa [hA.closure_eq] using hCl