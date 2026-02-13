

theorem P1_of_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure (interior (A : Set X)) = A) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  have : (x : X) ∈ closure (interior (A : Set X)) := by
    simpa [hEq] using hxA
  exact this