

theorem subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 (A : Set X))
    (hB : (B : Set X) ⊆ closure (A : Set X)) :
    (B : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hxB
  have hxClA : (x : X) ∈ closure (A : Set X) := hB hxB
  have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
    closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hEq] using hxClA