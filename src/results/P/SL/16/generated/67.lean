

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (⋃₀ 𝒜) := by
  classical
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hxUnion
  rcases Set.mem_sUnion.1 hxUnion with ⟨A, hA_mem, hxA⟩
  have hx_cl : x ∈ closure (interior A) := (h𝒜 A hA_mem) hxA
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have h_subset : A ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact interior_mono h_subset
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_cl