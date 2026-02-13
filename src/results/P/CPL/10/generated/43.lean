

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (A ∪ B ∪ C ∪ D) := by
  -- First, obtain `P2` for the union of the first three sets.
  have hABC : Topology.P2 (A ∪ B ∪ C) :=
    Topology.P2_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Combine this with `D`.
  simpa [Set.union_assoc] using
    (Topology.P2_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD)

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) : Topology.P3 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  -- Obtain `P3` for the product `A ×ˢ B ×ˢ C`.
  have hABC : Topology.P3 (Set.prod (Set.prod A B) C) :=
    Topology.P3_prod_three
      (X := W) (Y := X) (Z := Y)
      (A := A) (B := B) (C := C)
      hA hB hC
  -- Combine with `D` to get the required product.
  simpa using
    (Topology.P3_prod
        (X := (W × X) × Y) (Y := Z)
        (A := Set.prod (Set.prod A B) C) (B := D)
        hABC hD)