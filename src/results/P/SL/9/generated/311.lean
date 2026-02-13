

theorem Topology.disjoint_interior_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    Disjoint (interior (A : Set X)) (frontier A) := by
  -- We use `Set.disjoint_left`, which asks to prove that no element
  -- can belong to both sets simultaneously.
  exact (Set.disjoint_left).2 (by
    intro x hxInt hxFront
    -- From `hxFront : x ∈ frontier A = closure A \ interior A`
    -- we have `hxFront.2 : x ∉ interior A`, contradicting `hxInt`.
    exact hxFront.2 hxInt)