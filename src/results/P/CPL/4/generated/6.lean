

theorem P2_sUnion_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  -- Unfold the definition of `P2`
  dsimp [Topology.P2] at *
  intro x hx
  -- Pick a set `A ∈ 𝒜` with `x ∈ A`
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- `x` lies in `interior (closure (interior A))` by the hypothesis on `A`
  have hA_P2 : (A : Set X) ⊆ interior (closure (interior A)) := h A hA_mem
  have hx₁ : x ∈ interior (closure (interior A)) := hA_P2 hxA
  ----------------------------------------------------------------
  -- Monotonicity:  `interior (closure (interior A)) ⊆
  --                 interior (closure (interior ⋃₀ 𝒜))`
  ----------------------------------------------------------------
  -- First, `A ⊆ ⋃₀ 𝒜`
  have hA_subset_sUnion : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  -- Hence, `interior A ⊆ interior (⋃₀ 𝒜)`
  have h_int_subset :
      (interior A : Set X) ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset_sUnion
  -- Taking closures, then interiors again
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  have h_interior_closure_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono h_closure_subset
  ----------------------------------------------------------------
  -- Finish
  ----------------------------------------------------------------
  exact h_interior_closure_subset hx₁

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  -- First, prove that `closure A = univ`
  have h_closureA : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- `closure (interior A)` is the whole space by density
    have h_univ : (closure (interior A) : Set X) = Set.univ := h.closure_eq
    -- And `closure (interior A)` is contained in `closure A`
    have h_subset : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- Hence `univ ⊆ closure A`
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_univ] using h_subset
    -- Conclude the equality
    exact Set.Subset.antisymm (by
      intro y hy
      trivial) this
  -- With `closure A = univ`, its interior is also `univ`
  simpa [h_closureA, interior_univ]