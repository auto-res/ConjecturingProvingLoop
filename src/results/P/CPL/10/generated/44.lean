

theorem P2_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed (Aᶜ)) : Topology.P2 A := by
  -- Since `Aᶜ` is closed, its complement `A` is open.
  have hA_open : IsOpen (A : Set X) := by
    simpa [compl_compl] using h_closed.isOpen_compl
  -- Apply the lemma that open sets satisfy `P2`.
  exact Topology.P2_of_open (X := X) (A := A) hA_open

theorem P1_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) (hE : Topology.P1 E) : Topology.P1 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, obtain `P1` for `(A ×ˢ B) ×ˢ C`.
  have hABC : Topology.P1 (Set.prod (Set.prod A B) C) :=
    Topology.P1_prod_three (A := A) (B := B) (C := C) hA hB hC
  -- Combine with `D`.
  have hABCD : Topology.P1 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P1_prod
      (A := Set.prod (Set.prod A B) C) (B := D)
      hABC hD
  -- Combine with `E` to get the desired product.
  simpa using
    (Topology.P1_prod
      (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E)
      hABCD hE)