

theorem Topology.closure_inter_open_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : (closure A ∩ A : Set X) = A := by
  -- Start with the general identity `closure A ∩ interior A = interior A`.
  have h :=
    Topology.closure_inter_interior_eq_interior (X := X) (A := A)
  -- Rewrite `interior A` using the openness of `A`.
  simpa [hA.interior_eq] using h