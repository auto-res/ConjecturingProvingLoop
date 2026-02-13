

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A : Set X, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hP1
  intro x hx_sUnion
  rcases Set.mem_sUnion.1 hx_sUnion with ⟨A, hA_mem, hxA⟩
  have hx_closure : x ∈ closure (interior A) := (hP1 A hA_mem) hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    have hInt : (interior A : Set X) ⊆ interior (⋃₀ 𝒜) := by
      have hSub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact interior_mono hSub
    exact closure_mono hInt
  exact hsubset hx_closure