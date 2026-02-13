

theorem Topology.P3_implies_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP3 x hxFrontier
  -- A point in the frontier of `A` lies in `closure A`.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- `closure A` is contained in `closure (interior (closure A))` by `P3`.
  have hsubset :
      (closure (A : Set X)) ⊆ closure (interior (closure (A : Set X))) :=
    Topology.P3_implies_closure_subset_closure_interior_closure (A := A) hP3
  exact hsubset hx_closureA