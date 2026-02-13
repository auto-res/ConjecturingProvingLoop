

theorem Topology.isClosed_of_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : frontier A ⊆ A) : IsClosed A := by
  -- First, we show `closure A ⊆ A`.
  have hClosSub : closure A ⊆ A := by
    intro x hxClos
    -- Using `interior A ∪ frontier A = closure A`, we know that
    -- `x ∈ interior A ∪ frontier A`.
    have hxUnion : x ∈ interior A ∪ frontier A := by
      simpa [Topology.interior_union_frontier_eq_closure (A := A)] using hxClos
    -- We distinguish the two cases.
    cases hxUnion with
    | inl hInt =>
        -- `x ∈ interior A ⊆ A`
        exact (interior_subset : interior A ⊆ A) hInt
    | inr hFront =>
        -- `x ∈ frontier A ⊆ A` by the hypothesis `h`
        exact h hFront
  -- The inclusion `closure A ⊆ A` implies that `A` is closed.
  have hClosed : IsClosed A := by
    have hEquiv := (Topology.isClosed_iff_closure_subset (A := A))
    exact hEquiv.2 hClosSub
  simpa using hClosed