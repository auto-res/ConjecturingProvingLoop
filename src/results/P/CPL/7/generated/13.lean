

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hP1 x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := hP1 A hA_mem
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have h_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    have h_int_sub : interior A ⊆ interior (⋃₀ 𝒜) := interior_mono h_sub
    exact closure_mono h_int_sub
  exact h_subset hx_cl

theorem exists_dense_open_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → ∃ U, IsOpen U ∧ closure U = closure A := by
  intro hP3
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_⟩
  -- Prove `closure (interior (closure A)) = closure A`
  apply subset_antisymm
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h :
        closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono
        (show interior (closure A) ⊆ closure A from interior_subset)
    simpa [closure_closure] using h
  · -- `closure A ⊆ closure (interior (closure A))`
    have h : (A : Set X) ⊆ interior (closure A) := hP3
    exact closure_mono h

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := hP3 A hA_mem
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    -- `A ⊆ ⋃₀ 𝒜`
    have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    -- Apply monotonicity of `closure` and `interior`
    have h_cl_sub : closure A ⊆ closure (⋃₀ 𝒜) := closure_mono h_sub
    exact interior_mono h_cl_sub
  exact h_subset hx_int