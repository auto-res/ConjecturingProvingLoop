

theorem closure_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem P1_open_iff {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → (P1 A ↔ A ⊆ closure A) := by
  intro hA
  simpa [P1, hA.interior_eq]

theorem exists_open_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P1 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro _ _; trivial
  · exact P1_univ

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (mem_univ x)