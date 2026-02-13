

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P2_prod
        (X := X) (Y := Y)
        (A := A) (B := (Set.univ : Set Y))
        hA
        (Topology.P2_univ (X := Y)))