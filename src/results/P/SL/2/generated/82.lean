

theorem Topology.P3_iff_exists_open_superset_subset_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine
      ⟨interior (closure (A : Set X)), isOpen_interior,
        ?_, interior_subset⟩
    intro x hxA
    exact hP3 hxA
  · rintro ⟨U, hOpenU, hA_sub_U, hU_sub_cl⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    have hU_sub_int : U ⊆ interior (closure (A : Set X)) :=
      interior_maximal hU_sub_cl hOpenU
    exact hU_sub_int hxU