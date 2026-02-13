

theorem Topology.P2_implies_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P2 (X := X) A) :
    closure (A : Set X) = closure (interior A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hA
  exact Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1