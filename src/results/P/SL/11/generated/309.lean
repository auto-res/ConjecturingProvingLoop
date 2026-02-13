

theorem not_P2_of_interior_closure_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntClEmpty : interior (closure (A : Set X)) = (∅ : Set X))
    (hne : A.Nonempty) :
    ¬ Topology.P2 A := by
  intro hP2
  -- From `P2` we obtain `P3`.
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  -- Pick an element of the non-empty set `A`.
  rcases hne with ⟨x, hxA⟩
  -- `P3` sends it into `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- But this interior is empty, contradicting membership.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntClEmpty] using hxInt
  exact (Set.not_mem_empty _).elim this