

theorem Topology.frontier_eq_closure_interior_diff_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) →
      frontier A = closure (interior A) \ interior A := by
  intro hP1
  have hFrontierEq :=
    Topology.frontier_eq_frontier_interior_of_P1 (A := A) hP1
  calc
    frontier A = frontier (interior A) := hFrontierEq
    _ = closure (interior A) \ interior A := by
      simp [frontier, interior_interior]