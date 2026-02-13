

theorem Topology.interiorClosureInterior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` : from left to right.
    have hSub : closure (interior A) ⊆ A := by
      have : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hA.closure_eq] using this
    exact interior_mono hSub
  · -- `⊇` : from right to left.
    have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono hSub
    simpa [interior_interior] using this