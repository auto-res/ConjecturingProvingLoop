

theorem P2_iff_exists_open_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure (interior A) := by
  constructor
  · intro hP2
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, interior_subset⟩
    exact hP2
  · rintro ⟨U, hUopen, hAU, hUcl⟩
    dsimp [Topology.P2]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    have hUsub : U ⊆ interior (closure (interior A)) :=
      interior_maximal hUcl hUopen
    exact hUsub hxU