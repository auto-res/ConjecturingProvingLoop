

theorem P1_iff_P3_for_open_sets {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  constructor
  · intro _
    exact P3_open (A := A) hA
  · intro _
    exact P1_open (A := A) hA

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.prod (Set.prod A B) C) := by
  -- First obtain `P1` for the product `A ×ˢ B`
  have hAB : P1 (Set.prod A B) := P1_prod (A := A) (B := B) hA hB
  -- Then combine this with `C`
  have hABC : P1 (Set.prod (Set.prod A B) C) :=
    P1_prod (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (Set.prod (Set.prod A B) C) := by
  -- First obtain `P3` for the product `A ×ˢ B`
  have hAB : P3 (Set.prod A B) := P3_prod (A := A) (B := B) hA hB
  -- Then combine this with `C`
  have hABC : P3 (Set.prod (Set.prod A B) C) :=
    P3_prod (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem exists_open_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure (interior (closure A)) := by
  refine ⟨interior (closure A), isOpen_interior, hA, rfl⟩