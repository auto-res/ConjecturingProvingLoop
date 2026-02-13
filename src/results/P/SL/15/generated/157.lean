

theorem P2_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} :
    Topology.P2 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P2 B := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_right
        (X := X) (Y := Y) (B := B)) hProd
  · intro hB
    have hUniv : Topology.P2 (Set.univ : Set X) := Topology.P2_univ (X := X)
    simpa using
      (Topology.P2_prod
        (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)