

theorem P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure A) := by
  simpa using ((Topology.P2_closure_iff_open (A := A)).mpr hOpenCl)