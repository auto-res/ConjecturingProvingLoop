

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  unfold P3 at hA hB ⊢
  exact
    Set.union_subset
      (hA.trans <| interior_mono <| closure_mono Set.subset_union_left)
      (hB.trans <| interior_mono <| closure_mono Set.subset_union_right)

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P1 A) → P1 (⋃₀ 𝒜) := by
  intro hP1
  classical
  refine Set.sUnion_subset ?_
  intro A hA
  have hPA : P1 A := hP1 A hA
  have h1 : (A : Set X) ⊆ closure (interior A) := hPA
  have h2 : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono (interior_mono (Set.subset_sUnion_of_mem hA))
  exact h1.trans h2

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P2 A) → P2 (⋃₀ 𝒜) := by
  intro hP2
  unfold P2 at hP2 ⊢
  refine Set.sUnion_subset ?_
  intro B hB
  have hPB : (B : Set X) ⊆ interior (closure (interior B)) := hP2 B hB
  have h2 :
      interior (closure (interior B)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono <| closure_mono <| interior_mono <| Set.subset_sUnion_of_mem hB
  exact hPB.trans h2

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  simpa [P1, interior_interior] using
    (subset_closure : (interior A : Set X) ⊆ closure (interior A))

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  exact (P2_imp_P3 (interior A)) P2_interior