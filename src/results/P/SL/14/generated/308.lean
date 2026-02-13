

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 A := by
  intro hDense
  -- The closure of a dense set is the whole space, hence open.
  have hOpenClosure : IsOpen (closure (A : Set X)) :=
    Topology.isOpen_closure_of_dense (X := X) (A := A) hDense
  -- An open closure implies `P3` for the original set.
  exact
    Topology.P3_of_isOpen_closure (X := X) (A := A) hOpenClosure