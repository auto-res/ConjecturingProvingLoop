

theorem P1_iff_closure_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) ↔ closure (interior (A : Set X)) = A := by
  constructor
  · intro hP1
    exact closure_interior_eq_of_isClosed_and_P1 (A := A) hA_closed hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have : (x : X) ∈ closure (interior (A : Set X)) := by
      simpa [hEq] using hx
    exact this