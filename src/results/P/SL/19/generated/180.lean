

theorem Topology.closure_diff_frontier_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ frontier A = interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClos, hxNotFront⟩
    -- If `x ∈ closure A` but not in the frontier, then it must lie in the interior.
    by_contra hNotInt
    have hFront : x ∈ frontier A := And.intro hxClos hNotInt
    exact hxNotFront hFront
  · intro hxInt
    have hxClos : x ∈ closure A :=
      (Topology.interior_subset_closure (A := A)) hxInt
    have hxNotFront : x ∉ frontier A := by
      intro hFront
      exact hFront.2 hxInt
    exact And.intro hxClos hxNotFront