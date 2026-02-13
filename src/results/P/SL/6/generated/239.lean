

theorem open_closure_iff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      closure (A : Set X) ⊆ interior (closure A) := by
  constructor
  · intro hOpen
    -- For an open set, its interior equals itself.
    have hEq : interior (closure (A : Set X)) = closure A :=
      hOpen.interior_eq
    -- Rewrite the reflexive inclusion using this equality.
    simpa [hEq] using
      (subset_rfl : closure (A : Set X) ⊆ closure A)
  · intro hSub
    -- Upgrade the given inclusion to an equality.
    have hEq : interior (closure (A : Set X)) = closure A :=
      Set.Subset.antisymm interior_subset hSub
    -- The interior of any set is open; use this to conclude.
    have hOpenInt : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using hOpenInt