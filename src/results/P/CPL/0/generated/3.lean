

theorem exists_max_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P1 B ∧ (∀ C : Set X, B ⊆ C → C ⊆ A → P1 C → C = B) := by
  classical
  -- `E` is the family of all subsets of `A` that satisfy `P1`.
  let E : Set (Set X) := {B | (B ⊆ A) ∧ P1 B}
  -- `B` is the union of all sets in `E`.
  let B : Set X := ⋃₀ E

  -- Step 1:  `B ⊆ A`.
  have hBsubsetA : (B : Set X) ⊆ A := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCmem, hxC⟩
    have hCsubA : (C : Set X) ⊆ A := by
      have h := hCmem
      dsimp [E] at h
      exact h.1
    exact hCsubA hxC

  -- Step 2:  `P1 B`.
  have hBP1 : P1 B := by
    intro x hxB
    rcases Set.mem_sUnion.1 hxB with ⟨C, hCmem, hxC⟩
    -- `C` itself satisfies `P1`.
    have hC_P1 : P1 (C : Set X) := by
      have h := hCmem
      dsimp [E] at h
      exact h.2
    have hx_clC : x ∈ closure (interior (C : Set X)) := hC_P1 hxC
    -- `C ⊆ B`
    have hCsubB : (C : Set X) ⊆ B := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨C, hCmem, hy⟩
    -- Monotonicity of `interior` and `closure`.
    have h_int_mono : interior (C : Set X) ⊆ interior B :=
      interior_mono hCsubB
    have h_cl_mono :
        closure (interior (C : Set X)) ⊆ closure (interior B) :=
      closure_mono h_int_mono
    exact h_cl_mono hx_clC

  -- Step 3:  maximality of `B`.
  have hMax :
      ∀ C : Set X, B ⊆ C → C ⊆ A → P1 C → C = B := by
    intro C hBC hCA hP1C
    -- `C` is also in `E`, hence `C ⊆ B`.
    have hCmem : C ∈ E := by
      dsimp [E]
      exact And.intro hCA hP1C
    have hCsubB : C ⊆ B := by
      intro x hxC
      exact Set.mem_sUnion.2 ⟨C, hCmem, hxC⟩
    exact subset_antisymm hCsubB hBC

  -- Assemble the result.
  exact ⟨B, hBsubsetA, hBP1, hMax⟩