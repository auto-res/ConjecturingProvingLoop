

theorem boundary_eq_empty_iff_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) ↔
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  constructor
  · intro hEmpty
    -- `closure A ⊆ interior A`
    have hCl_subset_int : closure (A : Set X) ⊆ interior (A : Set X) := by
      intro x hxCl
      by_cases hInt : (x : X) ∈ interior (A : Set X)
      · exact hInt
      ·
        have hMem : (x : X) ∈ closure (A : Set X) \ interior (A : Set X) :=
          ⟨hxCl, hInt⟩
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hEmpty] using hMem
        cases this
    -- `interior A ⊆ closure A`
    have hInt_subset_cl : interior (A : Set X) ⊆ closure (A : Set X) := by
      intro x hxInt
      exact subset_closure (interior_subset hxInt)
    -- `closure A = interior A`
    have hCl_eq_int : closure (A : Set X) = interior (A : Set X) :=
      Set.Subset.antisymm hCl_subset_int hInt_subset_cl
    -- `A ⊆ interior A`
    have hA_subset_int : (A : Set X) ⊆ interior (A : Set X) := by
      intro x hxA
      have hxCl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
      exact hCl_subset_int hxCl
    -- `interior A = A`
    have hInt_eq_A : interior (A : Set X) = A :=
      Set.Subset.antisymm interior_subset hA_subset_int
    -- `closure A = A`
    have hCl_eq_A : closure (A : Set X) = A := by
      apply Set.Subset.antisymm
      · intro x hxCl
        have : (x : X) ∈ interior (A : Set X) := hCl_subset_int hxCl
        exact interior_subset this
      · exact subset_closure
    -- `A` is open and closed
    have hOpen : IsOpen (A : Set X) := by
      simpa [hInt_eq_A] using (isOpen_interior : IsOpen (interior (A : Set X)))
    have hClosed : IsClosed (A : Set X) := by
      simpa [hCl_eq_A] using (isClosed_closure : IsClosed (closure (A : Set X)))
    exact And.intro hOpen hClosed
  · intro hClopen
    exact
      (boundary_eq_empty_of_isClopen (A := A) hClopen.1 hClopen.2)