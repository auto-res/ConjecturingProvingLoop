

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 A → P1 (Set.prod A (Set.univ : Set Y)) := by
  intro hP1A
  have hP1Univ : P1 (Set.univ : Set Y) := P1_univ
  simpa using (P1_product (A := A) (B := (Set.univ : Set Y)) hP1A hP1Univ)

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (Set.univ : Set Y)) := by
  intro hP2A
  simpa using
    (P2_product (A := A) (B := (Set.univ : Set Y)) hP2A
      (by
        simpa using (P2_univ : P2 (Set.univ : Set Y))))

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (Set.prod A (Set.univ : Set Y)) := by
  intro hP3A
  have hP3Univ : P3 (Set.univ : Set Y) := P3_univ
  simpa using (P3_product (A := A) (B := (Set.univ : Set Y)) hP3A hP3Univ)