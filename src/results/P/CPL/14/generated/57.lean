

theorem P2_prod_empty {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (A ×ˢ (∅ : Set Y)) := by
  intro hA
  simpa using
    (P2_prod (A := A) (B := (∅ : Set Y)) hA (by
      simpa using (P2_empty (X := Y))))

theorem P2_prod_empty_left {X Y} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 ((∅ : Set X) ×ˢ B) := by
  intro hB
  -- `P2` holds for the empty set on the left factor.
  have hEmpty : P2 (∅ : Set X) := by
    simpa using (P2_empty (X := X))
  -- Apply the product lemma for `P2`.
  simpa using
    (P2_prod (A := (∅ : Set X)) (B := B) hEmpty hB)

theorem P1_prod_empty_left {X Y} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P1 B → P1 ((∅ : Set X) ×ˢ B) := by
  intro hB
  -- `P1` holds for the empty set on the left factor.
  have hEmpty : P1 (∅ : Set X) := by
    simpa using (P1_empty (X := X))
  -- Apply the product lemma for `P1`.
  simpa using
    (P1_prod (A := (∅ : Set X)) (B := B) hEmpty hB)

theorem P3_prod_empty {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (A ×ˢ (∅ : Set Y)) := by
  intro hA
  have hEmpty : P3 (∅ : Set Y) := by
    simpa using (P3_empty (X := Y))
  simpa using (P3_prod (A := A) (B := (∅ : Set Y)) hA hEmpty)