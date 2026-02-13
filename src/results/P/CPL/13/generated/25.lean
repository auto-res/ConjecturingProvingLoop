

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := h A hA_mem
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact h_subset hx_in

theorem P3_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P3 (A i)) : Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP3i : Topology.P3 (A i) := h i
  have hx_in : x ∈ interior (closure (A i)) := hP3i hxAi
  have h_subset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact h_subset hx_in

theorem P1_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hC : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  -- Obtain `P2 A` from the closedness of `A` and the given `P3 A`
  have hP2 : Topology.P2 A :=
    ((Topology.P2_iff_P3_of_closed (A := A) hC).2 hP3)
  -- Conclude `P1 A` from `P2 A`
  exact Topology.P2_implies_P1 (A := A) hP2

theorem P3_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, ?_⟩
    · -- `A ⊆ interior (closure A)`
      dsimp [Topology.P3] at hP3
      exact hP3
    · -- `closure (interior (closure A)) = closure A`
      simpa using (closure_eq_of_P3 hP3).symm
  · rintro ⟨U, hU_open, hAU, h_cl⟩
    dsimp [Topology.P3]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    -- `U ⊆ interior (closure U)` since `U` is open and `U ⊆ closure U`
    have hU_to_interior : (U : Set X) ⊆ interior (closure U) :=
      interior_maximal (by
        intro y hy
        exact subset_closure hy) hU_open
    have hx_int_clU : x ∈ interior (closure U) := hU_to_interior hxU
    simpa [h_cl] using hx_int_clU

theorem P3_implies_P1_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h_eq : closure A = closure (interior A)) : Topology.P3 A → Topology.P1 A := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hxA
  have hx_cl : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) (hP3 hxA)
  simpa [h_eq] using hx_cl