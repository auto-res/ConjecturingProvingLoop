

theorem P1_prod_univ {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hA (by
      simpa using (P1_univ (X := Y))))

theorem P3_prod_univ {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : P3 (Set.univ : Set Y) := by
    simpa using (P3_of_open (A := (Set.univ : Set Y)) isOpen_univ)
  simpa using (P3_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)