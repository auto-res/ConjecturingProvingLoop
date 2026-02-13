

theorem exists_max_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P3 B ∧ (∀ C : Set X, B ⊆ C → C ⊆ A → P3 C → C = B) := by
  classical
  -- `E` is the collection of subsets of `A` satisfying `P3`.
  let E : Set (Set X) := {B | (B ⊆ A) ∧ P3 B}
  -- `B` is the union of all sets in `E`.
  let B : Set X := ⋃₀ E
  -- First, show `B ⊆ A`.
  have hBsubsetA : (B : Set X) ⊆ A := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCmem, hxC⟩
    dsimp [E] at hCmem
    exact hCmem.1 hxC
  -- Next, show `P3 B`.
  have hBP3 : P3 B := by
    have hFam : ∀ C ∈ E, P3 C := by
      intro C hCmem
      dsimp [E] at hCmem
      exact hCmem.2
    simpa [B] using (P3_sUnion hFam)
  -- Finally, establish maximality of `B`.
  have hMax :
      ∀ C : Set X, B ⊆ C → C ⊆ A → P3 C → C = B := by
    intro C hBC hCA hP3C
    -- `C` is an element of `E`, hence contained in `B`.
    have hCmem : C ∈ E := by
      dsimp [E]
      exact And.intro hCA hP3C
    have hCsubB : (C : Set X) ⊆ B := by
      intro x hxC
      exact Set.mem_sUnion.2 ⟨C, hCmem, hxC⟩
    exact Set.Subset.antisymm hCsubB hBC
  -- Assemble the result.
  exact ⟨B, hBsubsetA, hBP3, hMax⟩

theorem exists_min_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P2 B ∧ (∀ C : Set X, C ⊆ B → P2 C → C = B) := by
  refine ⟨(∅ : Set X), Set.empty_subset _, P2_empty, ?_⟩
  intro C hCsubset _hP2C
  exact subset_antisymm hCsubset (Set.empty_subset _)