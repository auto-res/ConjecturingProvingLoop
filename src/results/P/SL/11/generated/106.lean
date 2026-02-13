

theorem P3_closure_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P3 (closure A) := by
  simpa using (Topology.P3_closure_iff_open (A := A)).mpr hOpenCl