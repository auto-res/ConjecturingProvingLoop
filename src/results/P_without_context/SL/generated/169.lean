

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_subset : closure (interior A) ⊆ closure A := by
      have h_inner : interior A ⊆ A := interior_subset
      exact closure_mono h_inner
    exact interior_mono h_closure_subset
  exact subset_trans hP2 h_subset