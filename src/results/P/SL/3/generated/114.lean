

theorem interior_closure_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) =
        interior (closure (interior (closure (A : Set X)))) := by
  intro hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact interior_closure_eq_closure_interior_closure_of_P3 (A := A) hP3