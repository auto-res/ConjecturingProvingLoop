

theorem Topology.P2_iff_exists_open_superset_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure (interior A) := by
  constructor
  · intro hP2
    refine
      ⟨interior (closure (interior A)), isOpen_interior, ?_, interior_subset⟩
    intro x hxA
    exact hP2 hxA
  · rintro ⟨U, hOpenU, hA_sub_U, hU_sub_cl⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    have hU_sub_int : U ⊆ interior (closure (interior A)) :=
      interior_maximal hU_sub_cl hOpenU
    exact hU_sub_int hxU