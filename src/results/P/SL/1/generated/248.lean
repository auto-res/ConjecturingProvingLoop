

theorem Topology.P3_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P3 A := by
  -- A closed and dense set coincides with `univ`.
  have hEq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  -- `univ` trivially satisfies `P3`.
  have hP3_univ : Topology.P3 (Set.univ : Set X) :=
    P3_univ (X := X)
  -- Transfer the property via the set equality.
  simpa [hEq] using hP3_univ