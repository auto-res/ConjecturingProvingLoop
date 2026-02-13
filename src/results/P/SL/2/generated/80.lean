

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A : Set X, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hP3
  intro x hx_sUnion
  rcases Set.mem_sUnion.1 hx_sUnion with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (A : Set X)) := (hP3 A hA_mem) hxA
  have hsubset : interior (closure (A : Set X)) ⊆ interior (closure (⋃₀ 𝒜 : Set X)) := by
    have hcl : closure (A : Set X) ⊆ closure (⋃₀ 𝒜 : Set X) := by
      have hSub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact closure_mono hSub
    exact interior_mono hcl
  exact hsubset hx_int