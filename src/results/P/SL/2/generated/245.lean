

theorem Topology.P1_implies_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP1 x hxFrontier
  -- `x` lies in the closure of `A` by definition of the frontier.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- From `P1 A`, `closure A ⊆ closure (interior A)`.
  have hSub₁ :
      (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  have hx_closureIntA : x ∈ closure (interior A) := hSub₁ hx_closureA
  -- And `closure (interior A)` is contained in
  -- `closure (interior (closure A))`.
  have hSub₂ :
      (closure (interior A)) ⊆
        closure (interior (closure (A : Set X))) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  exact hSub₂ hx_closureIntA