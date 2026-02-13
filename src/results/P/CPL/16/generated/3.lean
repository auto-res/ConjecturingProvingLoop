

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  unfold P2 at hA hB ⊢
  exact
    Set.union_subset
      (hA.trans <|
        interior_mono <| closure_mono <| interior_mono Set.subset_union_left)
      (hB.trans <|
        interior_mono <| closure_mono <| interior_mono Set.subset_union_right)

theorem P3_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hA
  exact interior_maximal subset_closure hA

theorem exists_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P2 B := by
  exact ⟨(∅ : Set X), Set.empty_subset _, P2_empty⟩

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P3 A) → P3 (⋃₀ 𝒜) := by
  intro hP3
  classical
  refine Set.sUnion_subset ?_
  intro A hA
  have hPA : P3 A := hP3 A hA
  have h1 : (A : Set X) ⊆ interior (closure A) := hPA
  have h2 : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono (closure_mono (Set.subset_sUnion_of_mem hA))
  exact h1.trans h2