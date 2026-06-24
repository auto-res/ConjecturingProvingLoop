

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hP2.trans hsubset