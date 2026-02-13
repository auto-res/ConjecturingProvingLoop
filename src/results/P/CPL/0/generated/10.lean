

theorem exists_max_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P2 B ∧ (∀ C : Set X, B ⊆ C → C ⊆ A → P2 C → C = B) := by
  classical
  -- `E` is the family of all subsets of `A` that satisfy `P2`.
  let E : Set (Set X) := {B | (B ⊆ A) ∧ P2 B}
  -- `B` is the union of all sets in `E`.
  let B : Set X := ⋃₀ E
  -- Step 1:  `B ⊆ A`.
  have hBsubsetA : (B : Set X) ⊆ A := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCmem, hxC⟩
    dsimp [E] at hCmem
    exact hCmem.1 hxC
  -- Step 2:  `P2 B`.
  have hBP2 : P2 B := by
    have hFam : ∀ C ∈ E, P2 C := by
      intro C hCmem
      dsimp [E] at hCmem
      exact hCmem.2
    simpa [B] using (P2_sUnion hFam)
  -- Step 3:  maximality of `B`.
  have hMax :
      ∀ C : Set X, B ⊆ C → C ⊆ A → P2 C → C = B := by
    intro C hBC hCA hP2C
    -- `C` is also in `E`, hence `C ⊆ B`.
    have hCmem : C ∈ E := by
      dsimp [E]
      exact And.intro hCA hP2C
    have hCsubB : (C : Set X) ⊆ B := by
      intro x hxC
      exact Set.mem_sUnion.2 ⟨C, hCmem, hxC⟩
    exact subset_antisymm hCsubB hBC
  -- Assemble the result.
  exact ⟨B, hBsubsetA, hBP2, hMax⟩