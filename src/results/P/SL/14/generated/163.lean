

theorem Topology.closureInterior_sInter_subset
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    closure (interior (⋂₀ 𝒜 : Set X)) ⊆
      ⋂₀ ((fun S : Set X => closure (interior S)) '' 𝒜) := by
  intro x hx
  -- To show `x` lies in the big intersection, we prove it belongs to each
  -- member of the image of `𝒜` under `closure ∘ interior`.
  apply Set.mem_sInter.2
  intro S hS
  -- Destructure `hS` to obtain the originating set `T ∈ 𝒜` with `S = closure (interior T)`.
  rcases hS with ⟨T, hT𝒜, rfl⟩
  -- We have to prove `x ∈ closure (interior T)`.
  -- First, note `⋂₀ 𝒜 ⊆ T`.
  have h_incl : (⋂₀ 𝒜 : Set X) ⊆ T := by
    intro y hy
    exact (Set.mem_sInter.1 hy) T hT𝒜
  -- Hence `interior (⋂₀ 𝒜) ⊆ interior T` by monotonicity of `interior`.
  have h_int : interior (⋂₀ 𝒜 : Set X) ⊆ interior T :=
    interior_mono h_incl
  -- Taking closures preserves inclusions, yielding the desired containment.
  have h_closure : closure (interior (⋂₀ 𝒜 : Set X)) ⊆ closure (interior T) :=
    closure_mono h_int
  -- Apply this inclusion to `x`.
  exact h_closure hx