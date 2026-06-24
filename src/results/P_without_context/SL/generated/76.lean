

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  have h1 : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact subset_trans h h1