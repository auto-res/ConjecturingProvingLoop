

theorem P3_closed_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ closure A = interior (closure A) := by
  simpa [hA.closure_eq] using (P3_closed_iff (X := X) (A := A) hA)

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (Set.prod (Set.prod A B) (Set.prod C D)) := by
  -- First, obtain `P2` for the product `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Next, obtain `P2` for the product `C × D`.
  have hCD : Topology.P2 (Set.prod C D) :=
    P2_prod (X := Y) (Y := Z) (A := C) (B := D) hC hD
  -- Finally, apply the product lemma once more to get the desired result.
  simpa using
    (P2_prod (X := W × X) (Y := Y × Z)
      (A := Set.prod A B) (B := Set.prod C D) hAB hCD)