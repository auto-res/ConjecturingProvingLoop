

theorem P3_clopen_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA₁ : IsOpen A) (hA₂ : IsClosed A) : P3 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P3_of_open (A := A) hA₁

theorem P2_exists_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ U, IsOpen U ∧ U ⊆ A := by
  intro _
  exact ⟨interior A, isOpen_interior, interior_subset⟩