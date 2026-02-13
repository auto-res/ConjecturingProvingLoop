

theorem P2_iff_exists_open_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧
        U ⊆ interior (closure (interior A)) := by
  classical
  constructor
  · intro hP2
    refine
      ⟨interior (closure (interior (A : Set X))),
        isOpen_interior, ?_, ?_⟩
    · exact hP2
    · exact subset_rfl
  · rintro ⟨U, _hOpenU, hASubU, hUSub⟩
    dsimp [Topology.P2] at *
    exact hASubU.trans hUSub