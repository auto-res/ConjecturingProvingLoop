

theorem P2_Union_closed {X ι : Type*} [TopologicalSpace X] (s : ι → Set X) (hcl : ∀ i, IsClosed (s i)) (hP : ∀ i, Topology.P2 (A := s i)) : Topology.P2 (A := ⋃ i, s i) := by
  simpa using P2_iUnion (s := s) (h := hP)

theorem P2_prod_both_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : Topology.P2 (A := Set.prod (Set.univ : Set X) (Set.univ : Set Y)) := by
  simpa using
    (Topology.P2_product
      (X := X) (Y := Y)
      (A := (Set.univ : Set X)) (B := (Set.univ : Set Y))
      (hA := Topology.P2_univ (X := X))
      (hB := Topology.P2_univ (X := Y)))