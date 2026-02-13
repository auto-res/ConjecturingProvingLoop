

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P1_prod
        (X := X) (Y := Y)
        (A := A) (B := (Set.univ : Set Y))
        hA
        (Topology.P1_univ (X := Y)))

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 A) : Topology.P3 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P3_prod
        (X := X) (Y := Y)
        (A := A) (B := (Set.univ : Set Y))
        hA
        (Topology.P3_univ (X := Y)))