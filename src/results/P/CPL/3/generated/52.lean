

theorem P3_dense_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : DenseRange f) : P3 (Set.range f) := by
  exact
    P3_of_dense (A := Set.range f) (by
      simpa using hf.closure_eq)