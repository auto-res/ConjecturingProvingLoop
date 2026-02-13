

theorem P2_product_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (Set.prod (Set.prod A B) C) := by
  exact P2_prod (P2_prod hA hB) hC