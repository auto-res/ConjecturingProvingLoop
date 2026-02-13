

theorem subset_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (A : Set X) ⊆ interior (closure A) := by
  intro hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact Topology.subset_interior_closure_of_P3 (A := A) hP3