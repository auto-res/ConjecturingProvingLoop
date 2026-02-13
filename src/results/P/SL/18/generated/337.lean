

theorem closure_interior_eq_univ_of_P2_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hDense : Dense (A : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_interior_eq_univ_of_P1_and_dense (A := A) hP1 hDense