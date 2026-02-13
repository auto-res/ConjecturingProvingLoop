

theorem Topology.interior_inter_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ frontier A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxInt, hxFront⟩
    -- `hxFront` consists of membership in the closure and non-membership in the interior.
    exact (hxFront.2 hxInt).elim
  · exact Set.empty_subset _