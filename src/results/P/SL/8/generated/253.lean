

theorem interior_inter_eq_left_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  apply Set.Subset.antisymm
  ·
    have h :=
      interior_inter_subset_inter_interior (X := X) (A := A) (B := B)
    simpa [hA.interior_eq] using h
  ·
    have hOpen : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    have hSub : A ∩ interior B ⊆ A ∩ B := by
      intro x hx
      exact And.intro hx.1 (interior_subset hx.2)
    exact (interior_maximal hSub hOpen)