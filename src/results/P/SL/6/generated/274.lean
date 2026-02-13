

theorem open_of_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) → IsOpen (closure (interior A)) := by
  intro hP3
  simpa using (open_of_P3_closure (A := interior (A : Set X)) hP3)