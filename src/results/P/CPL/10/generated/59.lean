

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  -- First, obtain `P2` for the triple product `(A ×ˢ B) ×ˢ C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    Topology.P2_prod_three
      (A := A) (B := B) (C := C)
      hA hB hC
  -- Combine this with `D` to obtain the required fourfold product.
  simpa using
    (Topology.P2_prod
        (X := (W × X) × Y) (Y := Z)
        (A := Set.prod (Set.prod A B) C) (B := D)
        hABC hD)