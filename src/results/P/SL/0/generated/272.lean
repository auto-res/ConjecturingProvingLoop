

theorem P3_iff_forall_open_neighborhood {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔
      ∀ x ∈ (A : Set X), ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (A : Set X) := by
  -- Forward implication: construct a single open set that works for every point.
  constructor
  · intro hP3 x hxA
    refine
      ⟨interior (closure (A : Set X)), isOpen_interior, ?_, interior_subset⟩
    exact hP3 hxA
  -- Reverse implication: each point has an appropriate neighbourhood, hence lies in the interior.
  · intro h
    dsimp [Topology.P3]
    intro x hxA
    rcases h x hxA with ⟨U, hU_open, hxU, hU_sub⟩
    -- Any open set contained in `closure A` is contained in its interior.
    have hU_in_int :
        (U : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_maximal hU_sub hU_open
    exact hU_in_int hxU