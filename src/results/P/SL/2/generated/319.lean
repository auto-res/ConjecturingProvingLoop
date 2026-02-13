

theorem Topology.P2_of_frontier_subset_closure_interior_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (interior A) →
    Topology.P3 A → Topology.P2 A := by
  intro hFront hP3
  -- Obtain `P1 A` from the frontier hypothesis.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_frontier_subset_closure_interior (A := A) hFront
  -- Combine `P1 A` and `P3 A` to deduce `P2 A`.
  exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3