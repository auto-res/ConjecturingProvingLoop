

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (Set.prod (Set.prod A B) C) := by
  -- First obtain `P3` for the product `A × B`.
  have hAB : Topology.P3 (Set.prod A B) :=
    P3_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Then apply the two‐factor result once more.
  simpa using
    (P3_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hAB hC)

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) : Topology.P1 (Set.prod (Set.prod A B) (Set.prod C D)) := by
  -- First, obtain `P1` for the product `A × B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    P1_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Next, obtain `P1` for the product `C × D`.
  have hCD : Topology.P1 (Set.prod C D) :=
    P1_prod (X := Y) (Y := Z) (A := C) (B := D) hC hD
  -- Finally, combine the two products.
  simpa using
    (P1_prod (X := W × X) (Y := Y × Z)
      (A := Set.prod A B) (B := Set.prod C D) hAB hCD)

theorem P2_Union_monotone_nat {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (hmono : Monotone s) (h : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, s n) := by
  simpa using (P2_Union_countable (X := X) (s := s) h)