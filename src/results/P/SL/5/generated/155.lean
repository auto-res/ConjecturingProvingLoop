

theorem P1_of_closure_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A := by
  -- First obtain `P2` from the density assumption.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_closure_dense_interior (X := X) (A := A) h
  -- Then derive `P1` from `P2`.
  exact Topology.P2_implies_P1 (X := X) (A := A) hP2