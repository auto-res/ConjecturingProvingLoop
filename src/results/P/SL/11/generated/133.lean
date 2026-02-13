

theorem interior_inter_eq_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (A ∩ B) = interior A ∩ interior B := by
  apply subset_antisymm
  ·
    -- The forward inclusion holds for arbitrary sets.
    exact interior_inter_subset (A := A) (B := B)
  ·
    -- For the reverse inclusion, use `interior_maximal`.
    have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro x hx
      exact ⟨(interior_subset : interior A ⊆ A) hx.1,
        (interior_subset : interior B ⊆ B) hx.2⟩
    have hOpen : IsOpen (interior A ∩ interior B) :=
      isOpen_interior.inter isOpen_interior
    exact interior_maximal hSub hOpen