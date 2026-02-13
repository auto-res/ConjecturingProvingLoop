

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, Topology.P3 (X:=X) A) : Topology.P3 (X:=X) (⋃₀ 𝒜) := by
  classical
  -- Unfold the definition of `P3`
  unfold Topology.P3 at hA ⊢
  -- Take a point in the sUnion
  intro x hx
  -- Obtain the witness set `A`
  rcases hx with ⟨A, hA_mem, hxA⟩
  -- Use `P3` for this particular `A`
  have hx_int_clA : x ∈ interior (closure A) := hA A hA_mem hxA
  -- Show the needed inclusion of closures
  have h_subset : closure A ⊆ closure (⋃₀ 𝒜) := by
    apply closure_mono
    intro y hy
    exact ⟨A, hA_mem, hy⟩
  -- Monotonicity of `interior` yields the claim
  exact (interior_mono h_subset) hx_int_clA