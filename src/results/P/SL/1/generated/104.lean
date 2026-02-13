

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hA
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := (hA A hA_mem) hxA
  -- We show that this interior is contained in the desired one.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- Step 1: `interior A ⊆ interior (⋃₀ 𝒜)`
    have h₁ : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    have h₂ : interior A ⊆ interior (⋃₀ 𝒜) := interior_mono h₁
    -- Step 2: take closures
    have h₃ : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h₂
    -- Step 3: take interiors again
    exact interior_mono h₃
  exact hsubset hxInt