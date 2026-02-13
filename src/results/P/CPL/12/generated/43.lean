

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 (Set.prod (Set.prod A B) C) := by
  intro hA hB hC
  have hAB : P2 (Set.prod A B) := P2_prod (A := A) (B := B) hA hB
  exact P2_prod (A := Set.prod A B) (B := C) hAB hC