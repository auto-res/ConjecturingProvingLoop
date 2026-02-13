

theorem Topology.closure_interior_eq_univ_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (h_dense : closure A = Set.univ) :
    closure (interior A) = Set.univ := by
  have h_eq := Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  simpa [h_dense] using (h_eq.symm).trans h_dense