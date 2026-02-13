

theorem P3_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hA : closure A = Set.univ) : P3 B := by
  apply P3_of_exists_dense_subset
  exact ⟨A, hAB, hA⟩

theorem P2_prod_five {U V W X Y : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) (hE : P2 E) : P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := P2_prod (P2_prod_four hA hB hC hD) hE