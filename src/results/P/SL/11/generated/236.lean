

theorem P1_iff_exists_open_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  constructor
  · intro hP1
    refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
    simpa using hP1
  · rintro ⟨U, hUopen, hUsubA, hAclU⟩
    dsimp [Topology.P1]
    intro x hxA
    have hx_clU : x ∈ closure U := hAclU hxA
    have hUsubInt : (U : Set X) ⊆ interior A :=
      interior_maximal hUsubA hUopen
    have h_cl_subset : closure U ⊆ closure (interior A) :=
      closure_mono hUsubInt
    exact h_cl_subset hx_clU