

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hP2
  dsimp [P2, P3] at hP2
  have h₁ : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact subset_trans hP2 h₂