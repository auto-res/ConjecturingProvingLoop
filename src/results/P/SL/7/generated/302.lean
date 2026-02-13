

theorem Topology.interiorClosure_union_eq_union_interiorClosures
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure (B : Set X))) :
    interior (closure (A ∪ B : Set X)) =
      interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) := by
  -- Start from the existing equality expressed with closures.
  have h :=
    Topology.interiorClosure_union_eq_union_of_open_closures
      (A := A) (B := B) hA hB
  -- Rewrite the right‐hand side using `interior_eq` for the open closures.
  simpa [hA.interior_eq, hB.interior_eq] using h