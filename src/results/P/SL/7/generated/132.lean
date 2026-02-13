

theorem Topology.interiorClosure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  -- First, prove `closure A = univ`.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.Subset_univ _
    · intro x _
      -- Since `closure (interior A) = univ`, every point belongs to it.
      have hx_clInt : x ∈ closure (interior A) := by
        have : x ∈ (Set.univ : Set X) := by trivial
        simpa [h] using this
      -- And `closure (interior A) ⊆ closure A`.
      have hIncl : closure (interior A) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior A ⊆ (A : Set X))
      exact hIncl hx_clInt
  -- Taking interiors yields the desired equality.
  simpa [hClosureA, interior_univ]