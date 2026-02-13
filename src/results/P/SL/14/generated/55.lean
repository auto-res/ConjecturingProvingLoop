

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → Topology.P2 S) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  -- From `P2` for `S`, we know `x` lies in `interior (closure (interior S))`.
  have hx_int : (x : X) ∈ interior (closure (interior S)) := (h𝒜 S hS𝒜) hxS
  -- Show that `interior (closure (interior S)) ⊆ interior (closure (interior (⋃₀ 𝒜)))`.
  have h_incl : interior (closure (interior S)) ⊆
      interior (closure (interior (⋃₀ 𝒜))) := by
    -- We first show `closure (interior S) ⊆ closure (interior (⋃₀ 𝒜))`.
    have h_closure_mono : closure (interior S) ⊆ closure (interior (⋃₀ 𝒜)) := by
      -- This follows from `interior S ⊆ interior (⋃₀ 𝒜)`.
      have h_int_mono : interior S ⊆ interior (⋃₀ 𝒜) := by
        have h_subset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
          intro y hy
          exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
        exact interior_mono h_subset
      exact closure_mono h_int_mono
    -- Taking interiors yields the desired inclusion.
    exact interior_mono h_closure_mono
  exact h_incl hx_int