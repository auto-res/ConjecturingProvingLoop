

theorem P2_of_closure_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = Set.univ) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x _hxA
  -- Since `closure (interior A) = univ`, its interior is also `univ`.
  have : x ∈ interior (closure (interior (A : Set X))) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [h, interior_univ] using this
  exact this