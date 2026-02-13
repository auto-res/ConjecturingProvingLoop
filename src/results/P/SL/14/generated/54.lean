

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → Topology.P3 S) :
    Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  -- From `P3` for `S`, `x` lies in `interior (closure S)`.
  have hx_int : (x : X) ∈ interior (closure S) := (h𝒜 S hS𝒜) hxS
  -- Show `interior (closure S)` is contained in `interior (closure (⋃₀ 𝒜))`.
  have h_incl : interior (closure S) ⊆ interior (closure (⋃₀ 𝒜)) := by
    -- First, upgrade the inclusion on the level of closures.
    have h_closure_mono : closure S ⊆ closure (⋃₀ 𝒜) := by
      have h_subset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
      exact closure_mono h_subset
    -- Taking interiors yields the desired inclusion.
    exact interior_mono h_closure_mono
  exact h_incl hx_int