

theorem isOpen_of_frontier_subset_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ Aᶜ → IsOpen A := by
  intro hFront
  -- First, show `A ⊆ interior A`.
  have hSub : (A : Set X) ⊆ interior A := by
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · exact hxInt
    · -- Otherwise `x` lies in the frontier, contradicting the hypothesis.
      have hxFrontier : x ∈ frontier A := by
        have hxCl : x ∈ closure A := subset_closure hxA
        exact And.intro hxCl hxInt
      have hxCompl : x ∈ Aᶜ := hFront hxFrontier
      exact (hxCompl hxA).elim
  -- Hence `interior A = A`.
  have hEq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact hSub
  -- Conclude that `A` is open.
  simpa [hEq] using (isOpen_interior : IsOpen (interior A))