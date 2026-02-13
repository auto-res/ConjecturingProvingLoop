

theorem Topology.interior_inter_boundary_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ (closure A \ interior A) = (∅ : Set X) := by
  simpa using (Set.inter_diff_self (interior A) (closure A))