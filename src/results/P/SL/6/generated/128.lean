

theorem open_of_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ⊆ interior A → IsOpen A := by
  intro hA
  have h₁ : interior (A : Set X) ⊆ A := interior_subset
  have hEq : interior (A : Set X) = A := subset_antisymm h₁ hA
  simpa [hEq] using (isOpen_interior : IsOpen (interior (A : Set X)))