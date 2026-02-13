

theorem Topology.P1_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (interior A) → Topology.P1 (A ∪ B) := by
  intro hDense
  -- `A` itself satisfies `P1`.
  have hP1A : Topology.P1 A :=
    Topology.P1_of_dense_interior (A := A) hDense
  -- Since `interior A` is dense, its closure is the whole space.
  have hClosure : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence every element of `B` lies in `closure (interior A)`.
  have hSubset : (B : Set X) ⊆ closure (interior A) := by
    intro x hxB
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hClosure] using this
  -- Apply the existing lemma to conclude the result.
  exact
    Topology.P1_union_of_subset (A := A) (B := B) hP1A hSubset