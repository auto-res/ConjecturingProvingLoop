

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hA
  have hsub : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans hA hsub