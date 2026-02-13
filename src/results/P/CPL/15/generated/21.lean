

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  -- Unfold the definition of `P2`
  dsimp [P2]
  -- Apply monotonicity of `interior` to `subset_closure`
  simpa [interior_interior] using
    interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))

theorem exists_open_closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  rcases P3_exists_subset_open (A := A) hA with ⟨U, hU_open, hAU, hUcl_sub⟩
  refine ⟨U, hU_open, hAU, ?_⟩
  have h₁ : (closure U : Set X) ⊆ closure A := hUcl_sub
  have h₂ : (closure A : Set X) ⊆ closure U := closure_mono hAU
  exact Set.Subset.antisymm h₁ h₂

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ∪ B ∪ C) := by
  have hAB : P1 (A ∪ B) := P1_union hA hB
  have hABC : P1 ((A ∪ B) ∪ C) := P1_union hAB hC
  simpa [Set.union_assoc] using hABC