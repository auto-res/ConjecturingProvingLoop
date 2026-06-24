

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  dsimp [P2, P3] at *
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_inter : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_subset
  exact subset_trans hP2 h_inter