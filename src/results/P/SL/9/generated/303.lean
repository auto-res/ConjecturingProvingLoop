

theorem Topology.interior_frontier_eq_empty_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (frontier (A : Set X)) = (∅ : Set X) := by
  -- First, rewrite the frontier of a closed set.
  have hFrontier : frontier (A : Set X) = A \ interior A := by
    simpa [frontier, hA_closed.closure_eq]
  -- Show that the interior of `A \ interior A` is empty.
  have hEmpty : interior (A \ interior A : Set X) = (∅ : Set X) := by
    apply (Set.eq_empty_iff_forall_not_mem).2
    intro x hx
    -- Obtain an open neighbourhood `U` of `x` contained in `A \ interior A`.
    rcases (mem_interior).1 hx with ⟨U, hU_sub, hU_open, hxU⟩
    -- From the inclusion, `U ⊆ A`.
    have hU_subA : U ⊆ (A : Set X) := by
      intro y hy
      exact (hU_sub hy).1
    -- Hence `U ⊆ interior A`, by maximality of the interior.
    have hU_subIntA : U ⊆ interior A := interior_maximal hU_subA hU_open
    -- Therefore `x ∈ interior A`, contradicting `x ∉ interior A`.
    have hxIntA : x ∈ interior A := hU_subIntA hxU
    have hxNotIntA : x ∉ interior A := (hU_sub hxU).2
    exact hxNotIntA hxIntA
  -- Combine the two equalities.
  simpa [hFrontier] using hEmpty