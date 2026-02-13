

theorem P2_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (Set.univ : Set Y)) := by
  intro hP2A
  simpa using
    (P2_prod (A := A) (B := (Set.univ : Set Y)) hP2A (P2_univ (X := Y)))

theorem P3_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P3 B → P3 (Set.prod (Set.univ : Set X) B) := by
  intro hP3B
  simpa using
    (P3_prod (A := (Set.univ : Set X)) (B := B) (P3_univ (X := X)) hP3B)