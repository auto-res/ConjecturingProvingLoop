

theorem exists_open_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, (Set.subset_univ A), P3_univ (X := X)⟩

theorem P1_empty_iff {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P1_empty (X := X)

theorem P2_univ_iff {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P2_univ (X := X)