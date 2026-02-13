

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (Set.univ : Set Y)) := by
  -- `P2` holds for `Set.univ`, by a previous lemma.
  have hUniv : P2 (Set.univ : Set Y) := P2_univ (X := Y)
  -- Apply the product lemma for `P2` and simplify.
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (A ×ˢ (Set.univ : Set Y)) := by
  -- `P3` holds for `Set.univ` in any topological space.
  have hUniv : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  -- Apply the product lemma for `P3` and simplify.
  simpa using (P3_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)