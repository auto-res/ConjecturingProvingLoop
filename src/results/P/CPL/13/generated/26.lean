

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) : Topology.P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, build `P2` for the triple product `A ×ˢ B ×ˢ C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    Topology.P2_prod_three hA hB hC
  -- Next, incorporate `D`, obtaining a quadruple product.
  have hABCD : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P2_prod hABC hD
  -- Finally, add `E` to reach the quintuple product.
  simpa using Topology.P2_prod hABCD hE

theorem P1_bool_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ Topology.P1 (Aᶜᶜ) := by
  have h : (Aᶜᶜ : Set X) = A := by
    ext x
    simp
  simpa [h]