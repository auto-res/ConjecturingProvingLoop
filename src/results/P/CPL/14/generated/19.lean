

theorem P2_to_P3_interior {X} [TopologicalSpace X] {A : Set X} : P2 A → P3 (interior A) := by
  intro _hP2
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  exact hsubset hx

theorem exists_dense_P2_subset {X} [TopologicalSpace X] {A : Set X} : Dense A → ∃ B, B ⊆ A ∧ P2 B := by
  intro _
  exact ⟨interior A, interior_subset, P2_interior_uncond (A := A)⟩