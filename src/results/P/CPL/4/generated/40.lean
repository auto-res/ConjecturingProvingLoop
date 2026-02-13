

theorem P2_prod_six {U V W X Y Z : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} {F : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) (hF : Topology.P2 F) : Topology.P2 (Set.prod (Set.prod (Set.prod A B) (Set.prod C D)) (Set.prod E F)) := by
  -- First, `P2` for the product `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := U) (Y := V) (A := A) (B := B) hA hB
  -- Next, `P2` for the product `C × D`.
  have hCD : Topology.P2 (Set.prod C D) :=
    P2_prod (X := W) (Y := X) (A := C) (B := D) hC hD
  -- Combine the two to obtain `P2` for `(A × B) × (C × D)`.
  have hABCD : Topology.P2 (Set.prod (Set.prod A B) (Set.prod C D)) :=
    P2_prod
      (X := U × V) (Y := W × X)
      (A := Set.prod A B) (B := Set.prod C D)
      hAB hCD
  -- `P2` for the product `E × F`.
  have hEF : Topology.P2 (Set.prod E F) :=
    P2_prod (X := Y) (Y := Z) (A := E) (B := F) hE hF
  -- Finally, combine once more to get the desired six–fold product.
  simpa using
    (P2_prod
      (X := (U × V) × (W × X))
      (Y := Y × Z)
      (A := Set.prod (Set.prod A B) (Set.prod C D))
      (B := Set.prod E F)
      hABCD
      hEF)