

theorem P1_prod_distrib_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hAB : P1 (Set.prod A B)) (hC : P1 C) : P1 (Set.prod A (Set.prod B C)) := by
  -- Step 1: obtain `P1` for `(A ×ˢ B) ×ˢ C`.
  have h₁ : P1 (Set.prod (Set.prod A B) C) := P1_prod hAB hC
  -- Step 2: use associativity of the product to transfer the property.
  have h₂ : P1 (Set.prod A (Set.prod B C)) :=
    (P1_prod_assoc (A := A) (B := B) (C := C)).1 h₁
  simpa using h₂

theorem P2_prod_distrib_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hAB : P2 (Set.prod A B)) (hC : P2 C) : P2 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P2` for `(A ×ˢ B) ×ˢ C`.
  have h₁ : P2 (Set.prod (Set.prod A B) C) := P2_prod hAB hC
  -- Use associativity of the product to transport the property.
  have h₂ : P2 (Set.prod A (Set.prod B C)) :=
    (P2_prod_assoc (A := A) (B := B) (C := C)).1 h₁
  simpa using h₂

theorem P3_prod_distrib_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hAB : P3 (Set.prod A B)) (hC : P3 C) : P3 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P3` for `(A ×ˢ B) ×ˢ C`.
  have h₁ : P3 (Set.prod (Set.prod A B) C) := P3_prod hAB hC
  -- Use associativity of the product to transport the property.
  have h₂ : P3 (Set.prod A (Set.prod B C)) :=
    (P3_prod_assoc (A := A) (B := B) (C := C)).1 h₁
  simpa using h₂