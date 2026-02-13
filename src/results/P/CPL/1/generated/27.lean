

theorem P2_sigma {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  simpa using P2_unionᵢ (A := A) h

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (Set.prod A (Set.prod B C)) := by
  -- First derive `P3` for the product `B × C`.
  have hBC : P3 (Set.prod B C) := P3_prod (A := B) (B := C) hB hC
  -- Then apply `P3_prod` once more to get the desired result.
  exact P3_prod (A := A) (B := Set.prod B C) hA hBC