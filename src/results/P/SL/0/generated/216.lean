

theorem P2_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧
        U ⊆ closure (interior (A : Set X)) := by
  dsimp [Topology.P2]
  constructor
  · intro hP2
    refine
      ⟨interior (closure (interior (A : Set X))), isOpen_interior, hP2, ?_⟩
    exact interior_subset
  · rintro ⟨U, hU_open, hA_sub_U, hU_sub_cl⟩
    have hU_sub_int :
        (U : Set X) ⊆ interior (closure (interior (A : Set X))) :=
      interior_maximal hU_sub_cl hU_open
    exact hA_sub_U.trans hU_sub_int