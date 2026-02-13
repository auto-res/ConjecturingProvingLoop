

theorem P1_iff_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔
      ∃ U : Set X, IsOpen U ∧ (U ⊆ A) ∧ (A : Set X) ⊆ closure U := by
  constructor
  · intro hP1
    refine
      ⟨interior (A : Set X), isOpen_interior, interior_subset, ?_⟩
    simpa [Topology.P1] using hP1
  · rintro ⟨U, hU_open, hU_sub_A, hA_sub_clU⟩
    dsimp [Topology.P1]
    have hU_sub_intA : (U : Set X) ⊆ interior (A : Set X) :=
      interior_maximal hU_sub_A hU_open
    have h_clU_sub :
        closure (U : Set X) ⊆ closure (interior (A : Set X)) :=
      closure_mono hU_sub_intA
    intro x hxA
    have hx_clU : x ∈ closure (U : Set X) := hA_sub_clU hxA
    exact h_clU_sub hx_clU