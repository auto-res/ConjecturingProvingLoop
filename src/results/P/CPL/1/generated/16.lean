

theorem P2_of_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := (P1_and_P3_iff_P2 (A := A)).1 ⟨h1, h3⟩

theorem P3_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : P3 A := by
  intro x hx
  exact h (subset_closure hx)

theorem exists_P2_between {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : ∃ B : Set X, A ⊆ B ∧ P2 B := by
  refine ⟨(Set.univ : Set X), ?_, P2_univ⟩
  ·
    intro x hx
    simp