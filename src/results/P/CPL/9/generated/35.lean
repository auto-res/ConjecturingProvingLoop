

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) : Topology.P2 (A := Set.prod A (Set.prod B C)) := by
  -- First, obtain `P2` for the product `B × C` in the space `Y × Z`.
  have hBC : Topology.P2 (A := Set.prod B C) := by
    simpa using
      (Topology.P2_product (X := Y) (Y := Z) (A := B) (B := C) hB hC)
  -- Now apply the two–factor product lemma with `A` and `B × C`.
  simpa using
    (Topology.P2_product
        (X := X) (Y := Y × Z)
        (A := A) (B := Set.prod B C) hA hBC)