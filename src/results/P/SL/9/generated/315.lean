

theorem Topology.closure_diff_frontier_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (A : Set X) \ frontier A = A := by
  classical
  -- Use the description of the frontier for open sets.
  have h_front : frontier (A : Set X) = closure A \ A :=
    Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA
  -- First, show `closure A \ frontier A ⊆ A`.
  have h_sub : closure A \ frontier A ⊆ A := by
    intro x hx
    rcases hx with ⟨hx_cl, hx_not_front⟩
    by_cases hxa : x ∈ A
    · exact hxa
    · have : x ∈ closure A \ A := ⟨hx_cl, hxa⟩
      have : x ∈ frontier (A : Set X) := by
        simpa [h_front] using this
      exact (hx_not_front this).elim
  -- Next, show `A ⊆ closure A \ frontier A`.
  have h_sup : (A : Set X) ⊆ closure A \ frontier A := by
    intro x hxA
    have hx_cl : x ∈ closure A := subset_closure hxA
    have hx_not_front : x ∉ frontier (A : Set X) := by
      intro hfront
      have : x ∈ closure A \ A := by
        simpa [h_front] using hfront
      exact this.2 hxA
    exact ⟨hx_cl, hx_not_front⟩
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h_sub h_sup