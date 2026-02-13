

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset

theorem P3_of_open {A : Set X} (hA : IsOpen A) : P3 A := by
  dsimp [P3]
  exact interior_maximal subset_closure hA

theorem P2_of_open {A : Set X} (hA : IsOpen A) : P2 A := by
  dsimp [P2]
  simpa [hA.interior_eq] using (P3_of_open hA)