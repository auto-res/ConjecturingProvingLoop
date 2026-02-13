

theorem Topology.isOpen_and_isClosed_of_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier A = (∅ : Set X) → IsOpen A ∧ IsClosed A := by
  intro hFrontier
  -- Step 1: show `closure A ⊆ interior A`
  have hClosSubInt : closure A ⊆ interior A := by
    intro x hxClos
    by_cases hInt : x ∈ interior A
    · exact hInt
    ·
      have hFront : x ∈ frontier A := And.intro hxClos hInt
      have : False := by
        simpa [hFrontier] using hFront
      exact this.elim
  -- Step 2: deduce `A ⊆ interior A`
  have hASubInt : (A : Set X) ⊆ interior A := by
    intro x hxA
    exact hClosSubInt (subset_closure hxA)
  -- Equalities `interior A = A` and `closure A = A`
  have hIntEq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact hASubInt
  have hClosEq : closure A = A := by
    apply Set.Subset.antisymm
    · intro x hxClos
      exact interior_subset (hClosSubInt hxClos)
    · exact subset_closure
  -- Conclude openness and closedness
  have hOpen : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [hIntEq] using this
  have hClosed : IsClosed A := by
    have : IsClosed (closure A) := isClosed_closure
    simpa [hClosEq] using this
  exact And.intro hOpen hClosed