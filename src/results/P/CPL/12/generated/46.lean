

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 (Set.prod (Set.prod A B) C) := by
  intro hA hB hC
  have hAB : P3 (Set.prod A B) := P3_prod (A := A) (B := B) hA hB
  exact P3_prod (A := Set.prod A B) (B := C) hAB hC

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P2 A → P2 B → P2 C → P2 D → P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hA hB hC hD
  have hABC : P2 (Set.prod (Set.prod A B) C) :=
    P2_prod_three (A := A) (B := B) (C := C) hA hB hC
  exact P2_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD