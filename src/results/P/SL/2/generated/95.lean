

theorem Topology.P1_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  constructor
  · intro hP1
    refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
    intro x hxA
    exact hP1 hxA
  · rintro ⟨U, hOpenU, hU_sub_A, hA_sub_clU⟩
    intro x hxA
    have hx_clU : x ∈ closure U := hA_sub_clU hxA
    have hU_sub_intA : (U : Set X) ⊆ interior A :=
      interior_maximal hU_sub_A hOpenU
    have h_clU_sub : (closure U : Set X) ⊆ closure (interior A) :=
      closure_mono hU_sub_intA
    exact h_clU_sub hx_clU