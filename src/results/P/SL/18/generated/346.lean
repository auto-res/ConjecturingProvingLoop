

theorem P3_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 (closure (A : Set X)) :=
  ((Topology.P3_closure_iff_open_closure (A := A)).mpr hOpen)