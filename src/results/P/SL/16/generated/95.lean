

theorem Topology.P2_iff_exists_open_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A ↔
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  classical
  constructor
  · intro hP2
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
    · exact hP2
    · exact subset_rfl
  · rintro ⟨U, _, hAU, hUsubset⟩
    dsimp [Topology.P2]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    exact hUsubset hxU