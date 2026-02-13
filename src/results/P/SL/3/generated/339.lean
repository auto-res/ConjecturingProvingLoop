

theorem subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (A ⊆ closure (interior (A : Set X))) := by
  intro hP2
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  simpa [Topology.P1] using hP1