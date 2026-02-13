

theorem Topology.P_properties_of_closed_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- A closed and dense set must coincide with the whole space.
  have hEq : A = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  -- All three properties hold for `Set.univ`; transport them along the equality.
  simpa [hEq] using (Topology.P_properties_univ (X := X))