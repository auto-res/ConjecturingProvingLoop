

theorem P3_univ_iff_true {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P3_univ (X := X)

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (Set.prod (Set.prod A B) C) := by
  -- First, get the `P2` property for `A ×ˢ B`.
  have hAB : P2 (Set.prod A B) := P2_prod (A := A) (B := B) hA hB
  -- Then, combine it with `C` to obtain the desired result.
  have hABC : P2 (Set.prod (Set.prod A B) C) :=
    P2_prod (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem exists_open_dense_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ U, IsOpen U ∧ U ⊆ A ∧ closure U = closure (interior A) := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  rfl