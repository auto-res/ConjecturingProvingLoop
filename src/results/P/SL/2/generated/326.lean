

theorem Topology.P3_implies_closure_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      closure (frontier (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
  intro hP3
  -- From `P3`, the frontier of `A` is already contained in
  -- `closure (interior (closure A))`.
  have hSub :
      (frontier (A : Set X) : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    Topology.P3_implies_frontier_subset_closure_interior_closure
      (A := A) hP3
  -- Taking closures preserves inclusions; simplify the right‐hand side.
  simpa [closure_closure] using closure_mono hSub