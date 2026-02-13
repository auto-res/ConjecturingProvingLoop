

theorem P1_prod_five {U V W Y Z : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set U} {B : Set V} {C : Set W} {D : Set Y} {E : Set Z} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) (hC : Topology.P1 (A := C)) (hD : Topology.P1 (A := D)) (hE : Topology.P1 (A := E)) : Topology.P1 (A := Set.prod A (Set.prod B (Set.prod C (Set.prod D E)))) := by
  -- First, obtain `P1` for `D × E` in the space `Y × Z`.
  have hDE : Topology.P1 (A := Set.prod D E) := by
    simpa using
      (Topology.P1_prod (A := D) (B := E) hD hE)
  -- Next, build `P1` for `C × (D × E)` in the space `W × (Y × Z)`.
  have hCDE : Topology.P1 (A := Set.prod C (Set.prod D E)) := by
    simpa using
      (Topology.P1_prod (A := C) (B := Set.prod D E) hC hDE)
  -- Then, construct `P1` for `B × (C × (D × E))` in the space
  -- `V × (W × (Y × Z))`.
  have hBCDE :
      Topology.P1 (A := Set.prod B (Set.prod C (Set.prod D E))) := by
    simpa using
      (Topology.P1_prod
        (A := B) (B := Set.prod C (Set.prod D E)) hB hCDE)
  -- Finally, combine with `A` to obtain the desired five–fold product.
  simpa using
    (Topology.P1_prod
      (A := A) (B := Set.prod B (Set.prod C (Set.prod D E))) hA hBCDE)

theorem P2_subset_closure_interior_closure {A : Set X} (hA : P2 A) : closure A ⊆ closure (interior (closure A)) := by
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    P2_subset_interior_closure (A := A) hA
  simpa using (closure_mono h_subset)

theorem P1_closed_complement {A : Set X} (hA : IsClosed A) : P1 Aᶜ := by
  exact P1_of_open (A := Aᶜ) hA.isOpen_compl