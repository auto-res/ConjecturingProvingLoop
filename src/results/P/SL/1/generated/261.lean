

theorem Topology.P1_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P1 A := by
  -- A closed and dense set coincides with the whole space.
  have hEq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  -- `P1` holds for `Set.univ`, hence it also holds for `A`.
  simpa [hEq] using (P1_univ (X := X))