

theorem P3_iff_exists_open_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧ U ⊆ closure (A : Set X) := by
  classical
  constructor
  · intro hP3
    refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
    · simpa using hP3
    · exact interior_subset
  · rintro ⟨U, hOpenU, hASubU, hUSub⟩
    dsimp [Topology.P3]
    have hU_into :
        U ⊆ interior (closure (A : Set X)) :=
      interior_maximal hUSub hOpenU
    exact hASubU.trans hU_into