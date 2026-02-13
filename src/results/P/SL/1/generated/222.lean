

theorem Topology.P3_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Dense A) :
    Topology.P3 (A ∪ B) := by
  -- `A` itself satisfies `P3`.
  have hP3A : Topology.P3 A := Topology.P3_of_dense (A := A) hA
  -- Since `A` is dense, `interior (closure A)` is the whole space.
  have hClosure : closure A = (Set.univ : Set X) := hA.closure_eq
  -- Hence every element of `B` lies in `interior (closure A)`.
  have hsubset : (B : Set X) ⊆ interior (closure A) := by
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hClosure, interior_univ] using this
  -- Apply the existing union lemma.
  exact Topology.P3_union_of_subset (A := A) (B := B) hP3A hsubset