

theorem P1_iff_exists_open_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  classical
  constructor
  · intro hP1
    refine ⟨interior (A : Set X), isOpen_interior, interior_subset, ?_⟩
    simpa using hP1
  · rintro ⟨U, hOpenU, hUSubA, hASubClosU⟩
    dsimp [Topology.P1]
    intro x hxA
    have hUSubInt : (U : Set X) ⊆ interior A :=
      interior_maximal hUSubA hOpenU
    have hxClosU : x ∈ closure U := hASubClosU hxA
    have hClosIncl : closure U ⊆ closure (interior A) :=
      closure_mono hUSubInt
    exact hClosIncl hxClosU