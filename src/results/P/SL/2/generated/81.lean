

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A : Set X, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hP2
  intro x hx_sUnion
  rcases Set.mem_sUnion.1 hx_sUnion with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := (hP2 A hA_mem) hxA
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) := by
    -- First, relate the interiors of `A` and `⋃₀ 𝒜`.
    have hInt : interior A ⊆ interior (⋃₀ 𝒜 : Set X) := by
      have hSub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact interior_mono hSub
    -- Take closures of both sides.
    have hCl : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜 : Set X)) :=
      closure_mono hInt
    -- Finally, take interiors again.
    exact interior_mono hCl
  exact hsubset hx_int