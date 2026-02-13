

theorem Topology.interior_eq_self_diff_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) = A \ frontier A := by
  classical
  apply Set.Subset.antisymm
  · intro x hx_int
    have hxA : x ∈ A := interior_subset hx_int
    have h_not_front : x ∉ frontier (A : Set X) := by
      intro h_front
      exact h_front.2 hx_int
    exact ⟨hxA, h_not_front⟩
  · intro x hx_diff
    rcases hx_diff with ⟨hxA, h_not_front⟩
    by_contra h_not_int
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    have hx_front : x ∈ frontier (A : Set X) := ⟨hx_cl, h_not_int⟩
    exact h_not_front hx_front