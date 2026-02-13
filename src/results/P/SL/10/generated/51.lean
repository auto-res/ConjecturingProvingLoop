

theorem Topology.closure_interior_eq_univ_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (h_dense : closure A = Set.univ) :
    closure (interior A) = Set.univ := by
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact
    Topology.closure_interior_eq_univ_of_P1 (X := X) (A := A) hP1 h_dense