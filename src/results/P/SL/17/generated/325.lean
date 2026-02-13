

theorem Topology.frontier_eq_empty_iff_isClosed_and_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ (IsClosed A ∧ IsOpen A) := by
  constructor
  · intro hEmpty
    -- From `frontier A = ∅` we have `closure A ⊆ interior A`
    have hSub : closure A ⊆ interior A := by
      intro x hxCl
      by_contra hxInt
      have : x ∈ closure A \ interior A := ⟨hxCl, hxInt⟩
      have : x ∈ (∅ : Set X) := by
        simpa [hEmpty] using this
      exact this.elim
    -- Show `closure A = A`
    have hClosEq : closure A = A := by
      apply Set.Subset.antisymm
      · intro x hx
        have : x ∈ interior A := hSub hx
        exact interior_subset this
      · exact subset_closure
    -- Show `interior A = A`
    have hIntEq : interior A = A := by
      apply Set.Subset.antisymm
      · intro x hx; exact interior_subset hx
      · intro x hx
        have : x ∈ closure A := subset_closure hx
        have : x ∈ interior A := hSub this
        exact this
    -- Conclude that `A` is both closed and open
    have hClosed : IsClosed A := by
      simpa [hClosEq] using (isClosed_closure : IsClosed (closure A))
    have hOpen : IsOpen A := by
      simpa [hIntEq] using (isOpen_interior : IsOpen (interior A))
    exact ⟨hClosed, hOpen⟩
  · rintro ⟨hClosed, hOpen⟩
    -- If `A` is clopen, its frontier is empty
    have hClos : closure A = A := hClosed.closure_eq
    have hInt  : interior A = A := hOpen.interior_eq
    simpa [frontier, hClos, hInt, Set.diff_self]