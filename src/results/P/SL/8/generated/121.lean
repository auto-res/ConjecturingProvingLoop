

theorem P3_nonempty_iff_interiorClosure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    A.Nonempty ↔ (interior (closure A)).Nonempty := by
  constructor
  · intro hA
    exact
      Topology.P3_nonempty_interiorClosure (X := X) (A := A) hP3 hA
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    -- From `hxInt : x ∈ interior (closure A)` we know `x ∈ closure A`.
    have hxCl : x ∈ closure A := interior_subset hxInt
    -- Use the characterization of points in the closure of `A`.
    have hIntersect :
        ((interior (closure A)) ∩ A).Nonempty := by
      have hMemClosure := (mem_closure_iff).1 hxCl
      simpa using hMemClosure (interior (closure A)) isOpen_interior hxInt
    -- Extract a witness from the non-empty intersection.
    rcases hIntersect with ⟨y, _, hyA⟩
    exact ⟨y, hyA⟩