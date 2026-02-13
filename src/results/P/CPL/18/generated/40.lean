

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A.prod (Set.univ : Set Y)) := by
  have hUniv : Topology.P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P2_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P2 B) : Topology.P2 ((Set.univ : Set X).prod B) := by
  have hUniv : Topology.P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using
    (P2_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)