

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (⋃₀ 𝒜) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at *
  intro x hx
  -- Obtain a set `A` from the union that contains `x`
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply the hypothesis `h` to `A`
  have hP1A : Topology.P1 A := h A hA_mem
  -- From `P1 A`, we know `x` is in the closure of the interior of `A`
  have hx_closure_intA : x ∈ closure (interior A) := hP1A hxA
  -- Show that `interior A ⊆ interior (⋃₀ 𝒜)`
  have h_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    -- First, note that `A ⊆ ⋃₀ 𝒜`
    have hA_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    -- Use monotonicity of `interior`
    exact interior_mono hA_subset
  -- Therefore, `closure (interior A) ⊆ closure (interior (⋃₀ 𝒜))`
  have h_closure_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_subset
  -- Conclude
  exact h_closure_subset hx_closure_intA