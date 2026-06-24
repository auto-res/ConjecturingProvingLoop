

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A :=
by
  intro hP2
  have h_closure : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h₁ : interior A ⊆ A := interior_subset
    have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
    exact interior_mono h₂
  exact subset_trans hP2 h_closure