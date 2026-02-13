

theorem P3_bUnion {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P3 (F i)) : P3 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_intFi : x ∈ interior (closure (F i)) := (h i) hxFi
  have hsubset_closure : closure (F i) ⊆ closure (⋃ j, F j) := by
    have : (F i : Set X) ⊆ ⋃ j, F j := Set.subset_iUnion _ _
    exact closure_mono this
  have hsubset_int :
      interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) :=
    interior_mono hsubset_closure
  exact hsubset_int hx_intFi

theorem exists_maximal_P3_subset {X} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P3 B ∧ ∀ C, C ⊆ A → P3 C → C ⊆ B := by
  classical
  -- Define the family of all `P3`-subsets of `A`.
  let ℱ : Set (Set X) := {C | C ⊆ A ∧ P3 C}
  -- Take their union as the candidate maximal set.
  refine ⟨⋃₀ ℱ, ?_, ?_, ?_⟩
  -- 1.  `⋃₀ ℱ ⊆ A`.
  · intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCℱ, hxC⟩
    exact (hCℱ.1) hxC
  -- 2.  `P3 (⋃₀ ℱ)`.
  ·
    have h_all : ∀ C, C ∈ ℱ → P3 C := by
      intro C hC
      exact hC.2
    exact P3_sUnion (ℱ := ℱ) h_all
  -- 3.  Maximality: every `P3` subset of `A` is contained in `⋃₀ ℱ`.
  · intro C hCsub hP3C
    have hCmem : C ∈ ℱ := ⟨hCsub, hP3C⟩
    intro x hx
    exact Set.mem_sUnion.2 ⟨C, hCmem, hx⟩