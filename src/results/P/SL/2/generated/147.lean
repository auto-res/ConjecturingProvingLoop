

theorem Topology.interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.interior_closure_subset_closure_interior_of_P1 (A := A) hP1