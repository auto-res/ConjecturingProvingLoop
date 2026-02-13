

theorem P3_iff_open_superset {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  constructor
  · intro hA
    exact exists_open_dense_subset_of_P3 hA
  · rintro ⟨U, hU_open, hAU, hclosure⟩
    exact P3_of_open_dense_subset hU_open hclosure hAU

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (A ×ˢ B ×ˢ C ×ˢ D) := by
  -- First, obtain `P3` for the product `B ×ˢ C ×ˢ D`.
  have hBCD : P3 (B ×ˢ C ×ˢ D) :=
    P3_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` using `P3_prod`.
  simpa using
    (P3_prod (A := A) (B := (B ×ˢ C ×ˢ D)) hA hBCD)

theorem P2_subsingleton (X : Type*) [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hx
  -- In a subsingleton space, every element equals `x`, so `A = univ`.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Hence the target interior is `univ`, so the inclusion holds.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hA_univ, interior_univ, closure_univ] using this