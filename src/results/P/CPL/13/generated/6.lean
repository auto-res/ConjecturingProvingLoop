

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact ⟨Topology.P2_implies_P1 hP2, Topology.P2_implies_P3 hP2⟩
  · rintro ⟨hP1, hP3⟩
    dsimp [Topology.P2] at *
    intro x hxA
    have hx : x ∈ interior (closure A) := hP3 hxA
    have h_closure_eq := Topology.closure_eq_of_P1 hP1
    simpa [h_closure_eq.symm] using hx

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := Set.mem_univ x
  simpa [h, interior_univ] using this

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP1i : Topology.P1 (A i) := h i
  have hx_cl : x ∈ closure (interior (A i)) := hP1i hxAi
  have h_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    -- First, show `A i ⊆ ⋃ j, A j`
    have hAi_subset : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    -- Then use monotonicity of `interior`
    exact interior_mono hAi_subset
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_subset
  exact h_closure_subset hx_cl

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P3 A) : Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := h A hA_mem
  have hx_in : x ∈ interior (closure A) := hP3A hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact h_subset hx_in