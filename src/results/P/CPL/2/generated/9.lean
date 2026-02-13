

theorem P2_Union {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P2 (X:=X) (A i)) : Topology.P2 (X:=X) (⋃ i, A i) := by
  classical
  -- unpack the definition of `P2`
  unfold Topology.P2 at h ⊢
  intro x hx
  -- choose an index witnessing `x ∈ ⋃ i, A i`
  rcases (Set.mem_iUnion).1 hx with ⟨i, hxAi⟩
  -- apply `P2` for this particular index
  have hi := h i
  -- `hi : A i ⊆ interior (closure (interior (A i)))`
  have hx₁ : x ∈ interior (closure (interior (A i))) := hi hxAi
  -- show the required inclusion of interiors
  have h_subset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    -- rely on monotonicity of `interior` and `closure`
    apply interior_mono
    have h_closure_subset :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      apply closure_mono
      have h_int_subset :
          interior (A i) ⊆ interior (⋃ j, A j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion_of_mem i hy
      exact h_int_subset
    exact h_closure_subset
  -- conclude
  exact h_subset hx₁

theorem P3_Union {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P3 (X:=X) (A i)) : Topology.P3 (X:=X) (⋃ i, A i) := by
  classical
  -- unpack the definition of `P3`
  unfold Topology.P3 at h ⊢
  intro x hx
  -- pick an index `i` such that `x ∈ A i`
  rcases (Set.mem_iUnion).1 hx with ⟨i, hxAi⟩
  -- use `P3` for this particular `i`
  have hx₁ : x ∈ interior (closure (A i)) := h i hxAi
  -- show the required inclusion of interiors
  have h_subset :
      interior (closure (A i)) ⊆
        interior (closure (⋃ j, A j)) := by
    -- rely on monotonicity of `interior` and `closure`
    apply interior_mono
    have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    exact h_closure_subset
  -- conclude
  exact h_subset hx₁

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (⋃₀ 𝒜) := by
  classical
  -- Unfold the definition of `P1`
  unfold Topology.P1 at hA ⊢
  -- Take an element of the sUnion
  intro x hx
  -- Obtain a witness set `A`
  rcases hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P1` for this particular `A`
  have hx_cl_intA : x ∈ closure (interior A) := hA A hA_mem hxA
  -- Show the needed inclusion of closures
  have h_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
      apply interior_mono
      intro y hy
      exact ⟨A, hA_mem, hy⟩
    exact h_int_subset
  -- Conclude
  exact h_subset hx_cl_intA