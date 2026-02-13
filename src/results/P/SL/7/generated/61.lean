

theorem Topology.P3_iff_exists_open_superset_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  classical
  unfold Topology.P3
  constructor
  · intro hP3
    exact ⟨interior (closure A), isOpen_interior, hP3, interior_subset⟩
  · rintro ⟨U, hU_open, hA_subU, hU_sub_cl⟩
    have hU_sub_int : U ⊆ interior (closure A) := interior_maximal hU_sub_cl hU_open
    intro x hxA
    exact hU_sub_int (hA_subU hxA)