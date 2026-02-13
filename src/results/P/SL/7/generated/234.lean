

theorem Topology.closureInterior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  -- From `P1` and non-emptiness of `A`, obtain a point in `interior A`.
  have hInt : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hA
  -- Any such point also belongs to `closure (interior A)`.
  rcases hInt with ⟨x, hxInt⟩
  exact ⟨x, subset_closure hxInt⟩