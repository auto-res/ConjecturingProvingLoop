

theorem P1_prod_empty {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (∅ : Set Y)) := by
  simpa using
    (P1_prod (A := A) (B := (∅ : Set Y)) hA (by
      simpa using (P1_empty (X := Y))))