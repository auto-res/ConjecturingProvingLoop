

theorem P2_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P2 B) : P2 (Set.prod (Set.univ : Set X) B) := by
  simpa using
    (P2_prod (A := (Set.univ : Set X)) (B := B) (P2_univ (X := X)) hB)

theorem P3_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P3 B) : P3 (Set.prod (Set.univ : Set X) B) := by
  simpa using
    (P3_prod (A := (Set.univ : Set X)) (B := B) (P3_univ (X := X)) hB)

theorem P1_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hA (P1_univ (X := Y)))

theorem P2_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (P2_prod (A := A) (B := (Set.univ : Set Y)) hA (P2_univ (X := Y)))

theorem P3_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (P3_prod (A := A) (B := (Set.univ : Set Y)) hA (P3_univ (X := Y)))