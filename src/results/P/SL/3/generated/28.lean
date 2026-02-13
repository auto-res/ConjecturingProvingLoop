

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔ closure (A : Set X) = closure (interior (A : Set X)) := by
  constructor
  · intro hA
    exact closure_eq_closure_interior_of_P1 (A := A) hA
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hx
    simpa [hEq] using hx_cl