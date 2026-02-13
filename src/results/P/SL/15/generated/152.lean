

theorem P3_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} :
    Topology.P3 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P3 B := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_right (X := X) (Y := Y) (B := B)) hProd
  · intro hB
    have hUniv : Topology.P3 (Set.univ : Set X) := Topology.P3_univ (X := X)
    have h := Topology.P3_prod
        (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB
    simpa using h