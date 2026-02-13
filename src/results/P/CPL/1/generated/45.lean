

theorem exists_P1_P2_P3 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P1 A ∧ P2 A ∧ P3 A := by
  refine ⟨(Set.univ : Set X), ?_⟩
  exact ⟨P1_univ (X := X), P2_univ (X := X), P3_univ (X := X)⟩

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) (hD : P1 D) : P1 (Set.prod A (Set.prod B (Set.prod C D))) := by
  -- Obtain `P1` for the product `B × (C × D)`.
  have hBCD : P1 (Set.prod B (Set.prod C D)) :=
    P1_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` to get the desired result.
  exact P1_prod (A := A) (B := Set.prod B (Set.prod C D)) hA hBCD

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (Set.prod A (Set.prod B (Set.prod C D))) := by
  -- Obtain `P2` for the product `B × (C × D)`.
  have hBCD : P2 (Set.prod B (Set.prod C D)) :=
    P2_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` to get the desired result.
  exact P2_prod (A := A) (B := Set.prod B (Set.prod C D)) hA hBCD

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (Set.prod A (Set.prod B (Set.prod C D))) := by
  -- First, obtain `P3` for the product `B × (C × D)`.
  have hBCD : P3 (Set.prod B (Set.prod C D)) :=
    P3_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` to get the desired result.
  exact P3_prod (A := A) (B := Set.prod B (Set.prod C D)) hA hBCD