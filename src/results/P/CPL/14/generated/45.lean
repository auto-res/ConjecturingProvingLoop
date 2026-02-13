

theorem P2_induction {X} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ B, IsClosed B ∧ x ∈ B ∧ B ⊆ A ∧ P2 B) : P2 A := by
  classical
  -- Define the family of all closed `P2`-subsets of `A`.
  let ℱ : Set (Set X) := {B | IsClosed B ∧ B ⊆ A ∧ P2 B}
  -- Every member of `ℱ` satisfies `P2`.
  have hP2_ℱ : ∀ B, B ∈ ℱ → P2 B := by
    intro B hB
    exact hB.2.2
  -- `P2` holds for the union of all sets in `ℱ`.
  have hP2_union : P2 (⋃₀ ℱ) :=
    P2_sUnion (ℱ := ℱ) hP2_ℱ
  -- The union of all sets in `ℱ` is exactly `A`.
  have h_union_eq : (⋃₀ ℱ : Set X) = A := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_sUnion.1 hx with ⟨B, hBℱ, hxB⟩
      exact (hBℱ.2.1) hxB
    · intro x hxA
      rcases h x hxA with ⟨B, hBclosed, hxB, hBsub, hBP2⟩
      have hBmem : B ∈ ℱ := by
        exact ⟨hBclosed, hBsub, hBP2⟩
      exact Set.mem_sUnion.2 ⟨B, hBmem, hxB⟩
  -- Transport `P2` through the equality.
  simpa [h_union_eq] using hP2_union