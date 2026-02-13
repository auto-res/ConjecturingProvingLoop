

theorem closureInterior_inter_interiorClosure_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : (A : Set X).Nonempty) :
    (closure (interior A) ∩ interior (closure (A : Set X))).Nonempty := by
  -- Choose a point `x` in `A`.
  rcases hA with ⟨x, hxA⟩
  -- From `P2` we obtain both `P1` and `P3`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Hence `x` belongs to both parts of the intersection.
  have hxClInt : x ∈ closure (interior A) := hP1 hxA
  have hxIntCl : x ∈ interior (closure (A : Set X)) := hP3 hxA
  exact ⟨x, ⟨hxClInt, hxIntCl⟩⟩