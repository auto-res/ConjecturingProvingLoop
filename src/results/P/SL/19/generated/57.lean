

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := closure A) := by
  intro hP2
  dsimp [Topology.P1]
  intro x hx
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  have hSub : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  have hx' : x ∈ closure (interior A) := by
    simpa [hEq] using hx
  exact hSub hx'