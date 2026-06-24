

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A ∧ P3 A := by
  intro h
  have hP1 : P1 A := by
    exact (Set.Subset.trans h interior_subset)
  have hP3 : P3 A := by
    have h₁ : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono (closure_mono interior_subset)
    exact (Set.Subset.trans h h₁)
  exact And.intro hP1 hP3