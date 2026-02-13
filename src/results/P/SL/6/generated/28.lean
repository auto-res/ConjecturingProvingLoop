

theorem closure_interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (A : Set X))) := by
  have hP1 : Topology.P1 (interior A) := Topology.interior_satisfies_P1 (A := A)
  have hP1' : Topology.P1 (closure (interior A)) :=
    Topology.P1_closure_of_P1 (A := interior A) hP1
  simpa using hP1'