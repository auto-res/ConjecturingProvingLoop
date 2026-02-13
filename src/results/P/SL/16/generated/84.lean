

theorem Topology.P3_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
    intro x hxA
    exact hP3 hxA
  · rintro ⟨U, hU_open, hA_U, hU_closure⟩
    dsimp [Topology.P3]
    intro x hxA
    have hxU : x ∈ U := hA_U hxA
    have hU_int : U ⊆ interior (closure A) :=
      interior_maximal hU_closure hU_open
    exact hU_int hxU