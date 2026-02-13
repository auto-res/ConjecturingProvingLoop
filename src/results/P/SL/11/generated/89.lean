

theorem P1_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure A) := by
  simpa using Topology.P1_of_open (A := closure A) hOpenCl