

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  -- First, deduce that `closure A = Set.univ`.
  have h_closureA : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`
    have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset (s := A))
    -- Hence, `Set.univ ⊆ closure A`
    have : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [hA] using h_subset
    -- Combine the two inclusions to obtain equality
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Apply the existing result for dense sets
  simpa using Topology.P3_of_dense (A := A) h_closureA