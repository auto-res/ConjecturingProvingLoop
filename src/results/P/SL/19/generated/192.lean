

theorem Topology.frontier_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → frontier A ⊆ closure (interior A) := by
  intro hP2
  -- `P2` implies `P1`
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
  -- Use the characterization of `P1` via the frontier
  exact
    (Topology.P1_iff_frontier_subset_closure_interior (A := A)).1 hP1