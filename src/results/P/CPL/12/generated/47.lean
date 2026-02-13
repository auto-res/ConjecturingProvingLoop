

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P1 A → P1 B → P1 C → P1 D → P1 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hA hB hC hD
  have hABC : P1 (Set.prod (Set.prod A B) C) :=
    P1_prod_three (A := A) (B := B) (C := C) hA hB hC
  exact
    P1_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P3 A → P3 B → P3 C → P3 D → P3 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hA hB hC hD
  have hABC : P3 (Set.prod (Set.prod A B) C) :=
    P3_prod_three (A := A) (B := B) (C := C) hA hB hC
  exact
    P3_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD