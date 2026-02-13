

theorem P3_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
    intro x hxA
    exact hP3 hxA
  · rintro ⟨U, hU_open, hAU, hUcl⟩
    dsimp [Topology.P3]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    have hU_in : U ⊆ interior (closure A) :=
      interior_maximal hUcl hU_open
    exact hU_in hxU