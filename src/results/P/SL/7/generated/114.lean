

theorem Topology.P2_iff_exists_open_superset_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  classical
  -- Unfold the definition of `P2`.
  unfold Topology.P2
  constructor
  · intro hP2
    -- Choose `U = interior (closure (interior A))`.
    refine ⟨interior (closure (interior A)), isOpen_interior, hP2, ?_⟩
    exact Set.Subset.rfl
  · rintro ⟨U, _hU_open, hA_subU, hU_sub⟩
    -- Use the two inclusions to obtain the desired one.
    intro x hxA
    exact hU_sub (hA_subU hxA)