

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  -- The interior of `closure A` is the whole space since `closure A = univ`.
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hDense] using interior_univ
  -- Hence any point, in particular `x`, lies in `interior (closure A)`.
  have : x ∈ interior (closure (A : Set X)) := by
    simpa [hInt] using (by
      simp : x ∈ (Set.univ : Set X))
  exact this