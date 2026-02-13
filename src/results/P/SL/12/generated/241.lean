

theorem Topology.P2_of_P1_and_isOpen_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A)
    (h_open : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (X := X) A := by
  -- Unfold `P2` to obtain the required subset relation.
  dsimp [Topology.P2] at *
  intro x hxA
  -- From `P1`, `x` lies in the closure of the interior of `A`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Since this closure is open, its interior is itself.
  have h_eq : interior (closure (interior (A : Set X))) =
      closure (interior A) := by
    simpa [h_open.interior_eq]
  -- Reinterpret the membership via the set equality.
  simpa [h_eq] using hx_cl