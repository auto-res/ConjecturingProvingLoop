

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  by_contra hInt
  -- If `interior A` were empty, its closure would also be empty.
  have hInt_empty : interior A = (∅ : Set X) := by
    simpa using (Set.not_nonempty_iff_eq_empty).1 hInt
  have hClIntEmpty : closure (interior A) = (∅ : Set X) := by
    simpa [hInt_empty] using closure_empty
  -- Pick any point of `A`.
  obtain ⟨x, hxA⟩ := hA
  -- `P1` says this point lies in the closure of `interior A`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- But that closure is empty: contradiction.
  have : x ∈ (∅ : Set X) := by
    simpa [hClIntEmpty] using hx_cl
  simpa using this