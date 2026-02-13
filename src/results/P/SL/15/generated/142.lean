

theorem P3_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} :
    Topology.P3 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P3 A := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_left
        (X := X) (Y := Y) (A := A)) hProd
  · intro hA
    exact
      (Topology.P3_prod_univ
        (X := X) (Y := Y) (A := A)) hA