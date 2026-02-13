

theorem P3_iff_exists_open_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, hP3, ?_⟩
    have h_subset : (interior (closure A) : Set X) ⊆ closure A :=
      interior_subset
    simpa [closure_closure] using (closure_mono h_subset)
  · rintro ⟨U, hU_open, hA_sub_U, h_closureU_sub_clA⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    -- `U ⊆ closure A`
    have hU_sub_clA : (U : Set X) ⊆ closure A := by
      intro y hyU
      have : (y : X) ∈ closure U := subset_closure hyU
      exact h_closureU_sub_clA this
    -- open set inside `closure A` lies in its interior
    have hU_sub_int : (U : Set X) ⊆ interior (closure A) :=
      interior_maximal hU_sub_clA hU_open
    exact hU_sub_int hxU