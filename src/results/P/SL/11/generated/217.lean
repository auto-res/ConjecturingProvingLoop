

theorem interior_closure_nonempty_iff_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    (interior (closure A)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hInt
    by_contra hA
    have hAeq : (A : Set X) = ∅ :=
      (Set.not_nonempty_iff_eq_empty).1 hA
    rcases hInt with ⟨x, hxInt⟩
    have hxCl : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxInt
    have : x ∈ (∅ : Set X) := by
      simpa [hAeq, closure_empty] using hxCl
    exact (Set.not_mem_empty x) this
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P1 (A := A) hP1 hA