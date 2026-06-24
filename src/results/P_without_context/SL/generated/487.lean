

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → (P1 A ∧ P3 A) := by
  intro hP2
  have hP1 : P1 A := by
    dsimp [P1]
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := by
      simpa using interior_subset (s := closure (interior A))
    exact Set.Subset.trans hP2 h₁
  have hP3 : P3 A := by
    dsimp [P3]
    have h_closure_mono : closure (interior A) ⊆ closure A := by
      exact closure_mono (interior_subset (s := A))
    have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h_closure_mono
    exact Set.Subset.trans hP2 h₂
  exact And.intro hP1 hP3