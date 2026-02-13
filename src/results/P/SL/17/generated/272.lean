

theorem Topology.frontier_interior_subset_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior A) ⊆ closure A \ interior A := by
  intro x hx
  -- First, upgrade `hx : x ∈ frontier (interior A)` to a membership in `frontier A`.
  have hFrontA : x ∈ frontier A :=
    (Topology.frontier_interior_subset_frontier (A := A)) hx
  -- Decompose `hFrontA` into the two required components.
  exact And.intro hFrontA.1 hFrontA.2