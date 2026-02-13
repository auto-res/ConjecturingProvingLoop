

theorem exists_compact_open_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ K, IsCompact K ∧ IsOpen K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, isOpen_empty, ?_⟩
  intro x hx
  cases hx

theorem P3_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) (hE : P3 E) : P3 (A ×ˢ B ×ˢ C ×ˢ D ×ˢ E) := by
  -- First, obtain `P3` for the product `B ×ˢ C ×ˢ D ×ˢ E`.
  have hBCDE : P3 (B ×ˢ C ×ˢ D ×ˢ E) :=
    P3_prod_four (A := B) (B := C) (C := D) (D := E) hB hC hD hE
  -- Combine with `A` using `P3_prod`.
  simpa using
    (P3_prod (A := A) (B := (B ×ˢ C ×ˢ D ×ˢ E)) hA hBCDE)

theorem P1_of_closure_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior A) : P1 A := by
  intro x hx
  -- From `x ∈ A` we have `x ∈ closure A`.
  have hx_int : x ∈ interior A := h (subset_closure hx)
  -- And `interior A ⊆ closure (interior A)`.
  exact (subset_closure : (interior A : Set X) ⊆ closure (interior A)) hx_int

theorem P2_prod_mixed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (interior (Set.univ : Set Y))) := by
  simpa [interior_univ] using
    (P2_prod_left (X := X) (Y := Y) (A := A) hA)