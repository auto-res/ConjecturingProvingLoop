

theorem boundary_eq_closure_interior_diff_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) \ interior (A : Set X) =
        closure (interior (A : Set X)) \ interior (A : Set X) := by
  intro hP2
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  exact boundary_eq_closure_interior_diff_interior_of_P1 (A := A) hP1