

theorem Topology.P2_iff_forall_open_nbhd_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔
      ∀ x : X, x ∈ (A : Set X) →
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A) := by
  constructor
  · intro hP2 x hxA
    refine
      ⟨interior (closure (interior A)), isOpen_interior,
        ?_, interior_subset⟩
    exact hP2 hxA
  · intro h
    intro x hxA
    rcases h x hxA with ⟨U, hOpenU, hxU, hU_sub⟩
    have hU_sub_int :
        (U : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal hU_sub hOpenU
    exact hU_sub_int hxU