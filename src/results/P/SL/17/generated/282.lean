

theorem Topology.frontier_subset_closure_interior_iff_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure (interior A) ↔ closure (interior A) = closure A := by
  constructor
  · intro hSub
    -- We already have `closure (interior A) ⊆ closure A`.
    apply Set.Subset.antisymm
    ·
      exact closure_mono (interior_subset : interior A ⊆ A)
    ·
      intro x hxClosA
      by_cases hxInt : x ∈ interior A
      ·
        -- Case `x ∈ interior A`
        exact subset_closure hxInt
      ·
        -- Case `x ∉ interior A`, so `x ∈ frontier A`
        have hxFront : x ∈ frontier A := by
          exact And.intro hxClosA hxInt
        exact hSub hxFront
  · intro hEq
    -- Rewrite membership using the equality of closures.
    intro x hxFront
    have : x ∈ closure A := hxFront.1
    simpa [hEq] using this