

theorem Topology.interior_diff_self_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior (A \ interior A) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in `A` but not in `interior A`
    have hxDiff : x ∈ A \ interior A := interior_subset hx
    -- Any open set contained in `A` is contained in `interior A`
    have h_subset : interior (A \ interior A) ⊆ interior A := by
      have h_open : IsOpen (interior (A \ interior A)) := isOpen_interior
      have h_subA : interior (A \ interior A) ⊆ A := by
        intro y hy; exact (interior_subset hy).1
      exact interior_maximal h_subA h_open
    -- Hence `x ∈ interior A`, contradiction
    have hxIntA : x ∈ interior A := h_subset hx
    exact (hxDiff.2 hxIntA)
  · exact Set.empty_subset _