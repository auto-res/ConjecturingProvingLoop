

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → Topology.P1 S) :
    Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  -- From `P1` for `S`, `x` is in `closure (interior S)`.
  have hx_closure_int : (x : X) ∈ closure (interior S) :=
    (h𝒜 S hS𝒜) hxS
  -- Show that `closure (interior S)` is contained in `closure (interior (⋃₀ 𝒜))`.
  have h_incl : closure (interior S) ⊆ closure (interior (⋃₀ 𝒜)) := by
    -- First, upgrade the inclusion on the level of interiors.
    have h_subset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
    have h_int : interior S ⊆ interior (⋃₀ 𝒜) :=
      interior_mono h_subset
    -- Taking closures yields the desired inclusion.
    exact closure_mono h_int
  exact h_incl hx_closure_int