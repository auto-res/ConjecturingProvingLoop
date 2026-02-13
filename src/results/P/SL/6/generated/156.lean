

theorem P1_iff_exists_open_subset_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  classical
  constructor
  · intro hP1
    refine ⟨interior (A : Set X), isOpen_interior, interior_subset, ?_⟩
    -- From `P1` we have `closure (interior A) = closure A`.
    have hEq :=
      (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
    simpa using hEq
  · rintro ⟨U, hOpenU, hUSubA, hClosureEq⟩
    dsimp [Topology.P1]
    intro x hxA
    -- First, place `x` in `closure U` using the equality of closures.
    have hx_clU : x ∈ closure U := by
      have : x ∈ closure (A : Set X) := subset_closure hxA
      simpa [hClosureEq] using this
    -- Since `U ⊆ interior A`, its closure is contained in `closure (interior A)`.
    have hU_in_intA : (U : Set X) ⊆ interior A :=
      interior_maximal hUSubA hOpenU
    have hClSub : closure U ⊆ closure (interior A) :=
      closure_mono hU_in_intA
    exact hClSub hx_clU