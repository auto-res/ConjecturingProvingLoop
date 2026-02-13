

theorem Topology.interior_nonempty_iff_exists_open_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty ↔
      ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ U.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨interior A, isOpen_interior, interior_subset, ⟨x, hx⟩⟩
  · rintro ⟨U, hUopen, hUsub, ⟨x, hxU⟩⟩
    have hUsubInt : U ⊆ interior A :=
      interior_maximal hUsub hUopen
    exact ⟨x, hUsubInt hxU⟩