

theorem P2_prod_four_univ {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W] : Topology.P2 (Set.prod (Set.prod (Set.univ : Set X) (Set.univ : Set Y)) (Set.prod (Set.univ : Set Z) (Set.univ : Set W))) := by
  -- `P2` holds for the product `univ ×ˢ univ` over `X` and `Y`.
  have hXY : Topology.P2 (Set.prod (Set.univ : Set X) (Set.univ : Set Y)) :=
    Topology.P2_univ_prod (X := X) (Y := Y)
  -- Likewise for `Z` and `W`.
  have hZW : Topology.P2 (Set.prod (Set.univ : Set Z) (Set.univ : Set W)) :=
    Topology.P2_univ_prod (X := Z) (Y := W)
  -- Combine the two using the product rule for `P2`.
  simpa using
    (Topology.P2_prod
        (A := Set.prod (Set.univ : Set X) (Set.univ : Set Y))
        (B := Set.prod (Set.univ : Set Z) (Set.univ : Set W))
        hXY hZW)