

theorem Topology.P1_iff_closure_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)`, take closures of both sides.
    have : closure A ⊆ closure (closure (interior A)) :=
      closure_mono (hP1 : A ⊆ closure (interior A))
    simpa [closure_closure] using this
  · intro hClSub
    -- Use the inclusion on closures to obtain the original `P1`.
    dsimp [Topology.P1]
    intro x hxA
    have hxCl : (x : X) ∈ closure A := subset_closure hxA
    exact hClSub hxCl