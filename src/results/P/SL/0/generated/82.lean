

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro h𝒜
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hx_in : x ∈ interior (closure (interior (A : Set X))) :=
    h𝒜 A hA_mem hxA
  have h_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
  have h_int_sub :
      interior (A : Set X) ⊆ interior (⋃₀ 𝒜 : Set X) :=
    interior_mono h_subset
  have h_closure_sub :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) :=
    closure_mono h_int_sub
  have h_mono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) :=
    interior_mono h_closure_sub
  exact h_mono hx_in