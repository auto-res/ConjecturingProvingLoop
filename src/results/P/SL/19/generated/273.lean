

theorem Topology.frontier_eq_empty_iff_closure_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ closure A = interior A := by
  constructor
  · intro hFront
    -- Start from `interior A ∪ frontier A = closure A`
    have hUnion := Topology.interior_union_frontier_eq_closure (A := A)
    -- Replace `frontier A` with `∅`
    have h' : interior A ∪ (∅ : Set X) = closure A := by
      simpa [hFront] using hUnion
    -- Simplify the left‐hand side
    have hEq : interior A = closure A := by
      simpa [Set.union_empty] using h'
    -- Reorient equality
    simpa using hEq.symm
  · intro hEq
    exact
      Topology.frontier_eq_empty_of_closure_eq_interior
        (A := A) hEq