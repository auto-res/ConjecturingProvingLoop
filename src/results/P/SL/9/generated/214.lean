

theorem Topology.P1_iff_boundary_subset_closureInterior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (A := A) ↔ (A \ interior A) ⊆ closure (interior A) := by
  classical
  -- First, show that `P1` implies the boundary inclusion.
  constructor
  · intro hP1
    -- We can reuse the general lemma and simplify using `hA_closed`.
    have h :=
      Topology.boundary_subset_closureInterior_of_P1 (A := A) hP1
    simpa [hA_closed.closure_eq] using h
  · intro hBoundary
    -- To prove `P1`, pick any `x ∈ A`.
    dsimp [Topology.P1] at *
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · -- Points of `interior A` are certainly in `closure (interior A)`.
      exact subset_closure hxInt
    · -- Otherwise `x` lies in the boundary, which is contained in the closure.
      have hx_boundary : x ∈ A \ interior A := ⟨hxA, hxInt⟩
      exact hBoundary hx_boundary