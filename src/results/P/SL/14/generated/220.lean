

theorem Topology.interior_sInter_subset
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    interior (⋂₀ 𝒜 : Set X) ⊆ ⋂₀ ((fun S : Set X => interior S) '' 𝒜) := by
  intro x hx
  -- For each `S ∈ 𝒜`, we have `x ∈ interior S`.
  have h₁ : ∀ S : Set X, S ∈ 𝒜 → (x : X) ∈ interior S := by
    intro S hS
    have h_subset : (⋂₀ 𝒜 : Set X) ⊆ S := by
      intro y hy
      exact (Set.mem_sInter.1 hy) S hS
    have h_int_mono :
        interior (⋂₀ 𝒜 : Set X) ⊆ interior S :=
      interior_mono h_subset
    exact h_int_mono hx
  -- Show that `x` lies in every element of the image `interior '' 𝒜`.
  have : ∀ T : Set X,
      T ∈ ((fun S : Set X => interior S) '' 𝒜) → (x : X) ∈ T := by
    intro T hT
    rcases hT with ⟨S, hS𝒜, rfl⟩
    exact h₁ S hS𝒜
  exact (Set.mem_sInter.2 this)