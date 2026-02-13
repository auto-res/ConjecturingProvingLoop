

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using (Set.mem_univ x)

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.prod (Set.prod A B) C) := by
  exact P1_prod (P1_prod hA hB) hC

theorem P2_prod_four {V W X Y : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  exact P2_prod (P2_product_three hA hB hC) hD

theorem P3_prod_four {V W X Y : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  exact P3_prod (P3_prod_three hA hB hC) hD