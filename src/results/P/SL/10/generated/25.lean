

theorem Topology.P3_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hA
    refine ⟨interior (closure A), isOpen_interior, hA, interior_subset⟩
  · rintro ⟨U, hUopen, hAU, hUcl⟩
    dsimp [Topology.P3]
    have hUsubset : U ⊆ interior (closure A) :=
      interior_maximal hUcl hUopen
    exact Set.Subset.trans hAU hUsubset