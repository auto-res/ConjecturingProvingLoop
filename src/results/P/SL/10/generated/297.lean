

theorem Topology.P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P1 A := by
  -- A closed and dense set coincides with the whole space.
  have h_eq : A = (Set.univ : Set X) := by
    have h_cl : closure A = A := hClosed.closure_eq
    simpa [h_cl] using h_dense
  -- `P1` holds for `Set.univ`, hence for `A`.
  simpa [h_eq] using (Topology.P1_univ (X := X))