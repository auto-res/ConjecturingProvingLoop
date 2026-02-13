

theorem Topology.P1_implies_frontier_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → frontier (A : Set X) ⊆ closure (interior A) := by
  intro hP1 x hxFrontier
  -- `x` lies in `closure A` by definition of the frontier.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- From `P1 A`, `closure A` is contained in `closure (interior A)`.
  have hsubset : (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  exact hsubset hx_closureA