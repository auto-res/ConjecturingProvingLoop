

theorem P1_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 A → P1 (Set.prod A (Set.univ : Set Y)) := by
  intro hP1A
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hP1A (P1_univ (X := Y)))

theorem P2_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hP2B
  simpa using
    (P2_prod (A := (Set.univ : Set X)) (B := B) (P2_univ (X := X)) hP2B)