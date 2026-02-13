

theorem Topology.P2_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  constructor
  · intro hP2
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
    · exact hP2
    · exact subset_rfl
  · rintro ⟨U, _hUopen, hAU, hUsubset⟩
    dsimp [Topology.P2]
    exact Set.Subset.trans hAU hUsubset