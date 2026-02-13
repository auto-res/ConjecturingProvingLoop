

theorem P2_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (Set.univ : Set Y)) := by
  have h_univ : P2 (Set.univ : Set Y) := P2_univ
  simpa using
    (P2_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem P3_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P3 B) : P3 ((Set.univ : Set X) ×ˢ B) := by
  simpa using
    (P3_prod (X := X) (Y := Y)
      (A := (Set.univ : Set X)) (B := B)
      (P3_univ (X := X)) hB)