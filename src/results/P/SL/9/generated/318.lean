

theorem Topology.inter_interior_frontier_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ frontier A = (∅ : Set X) := by
  classical
  -- We show that no point can belong to the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_int, hx_front⟩
  -- `hx_front.2` states that `x ∉ interior A`, contradicting `hx_int`.
  exact (hx_front.2) hx_int