

theorem frontier_eq_empty_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro hFrontierEmpty
    -- Step 1: translate `frontier A = ∅` into `closure A \ interior A = ∅`.
    have hDiffEmpty : closure A \ interior A = (∅ : Set X) := by
      have hEq := (frontier_eq_closure_diff_interior (X := X) (A := A)).symm
      simpa [hFrontierEmpty] using hEq
    -- Step 2: deduce `closure A ⊆ interior A`.
    have hSub : closure A ⊆ interior A := by
      intro x hxCl
      by_cases hxInt : x ∈ interior A
      · exact hxInt
      · have hxInDiff : x ∈ closure A \ interior A := And.intro hxCl hxInt
        have : x ∈ (∅ : Set X) := by
          simpa [hDiffEmpty] using hxInDiff
        exact (by cases this)
    -- Step 3: establish `closure A = interior A`.
    have hEq_cl_int : closure A = interior A := by
      apply Set.Subset.antisymm hSub
      -- `interior A ⊆ closure A`
      intro x hxInt
      have hxA : x ∈ A := interior_subset hxInt
      exact subset_closure hxA
    -- Step 4: derive `interior A = A` and `closure A = A`.
    have hIntEqA : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        have hxCl : x ∈ closure A := subset_closure hxA
        simpa [hEq_cl_int] using hxCl
    have hClEqA : closure A = A := by
      simpa [hIntEqA] using hEq_cl_int
    -- Step 5: conclude that `A` is both open and closed.
    have hOpen : IsOpen A := by
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hIntEqA] using hOpenInt
    have hClosed : IsClosed A := by
      have hClosedCl : IsClosed (closure A) := isClosed_closure
      simpa [hClEqA] using hClosedCl
    exact And.intro hOpen hClosed
  · rintro ⟨hOpen, hClosed⟩
    -- A set that is both open and closed has empty frontier.
    simpa using
      (frontier_eq_empty_of_clopen (A := A) hOpen hClosed)