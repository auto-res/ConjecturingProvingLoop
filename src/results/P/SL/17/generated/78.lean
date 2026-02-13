

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure A) := by
  -- `interior` is monotone, and `A` is always contained in its closure.
  exact interior_mono (subset_closure : A ⊆ closure A)