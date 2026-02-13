

theorem P1_subsingleton {X} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  simpa using (P1_of_P2 (A := A) P2_subsingleton)

theorem P2_prod_univ {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P2_prod (A := A) (B := (Set.univ : Set Y)) hA (by
      simpa using (P2_univ (X := Y))))