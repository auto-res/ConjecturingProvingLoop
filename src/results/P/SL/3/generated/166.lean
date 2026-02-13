

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : (A : Set X).Nonempty) (hP2 : Topology.P2 (A : Set X)) :
    (interior (A : Set X)).Nonempty := by
  classical
  by_contra hInt
  -- If `interior A` is empty, derive a contradiction with `P2`.
  have hInt_empty : interior (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  rcases hA with ⟨x, hxA⟩
  have hxInt : (x : X) ∈ interior (closure (interior (A : Set X))) :=
    hP2 hxA
  have : (x : X) ∈ (∅ : Set X) := by
    simpa [hInt_empty] using hxInt
  exact this