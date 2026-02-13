

theorem P3_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧ U ⊆ closure (A : Set X) := by
  dsimp [Topology.P3]
  constructor
  · intro hP3
    refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, interior_subset⟩
    exact hP3
  · rintro ⟨U, hU_open, hA_sub_U, hU_sub_cl⟩
    -- Any open set contained in `closure A` is contained in its interior.
    have hU_sub_int : (U : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_maximal hU_sub_cl hU_open
    -- Assemble the desired inclusion.
    intro x hxA
    exact hU_sub_int (hA_sub_U hxA)