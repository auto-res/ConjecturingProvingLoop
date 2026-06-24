

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hA
  exact hA.trans (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))