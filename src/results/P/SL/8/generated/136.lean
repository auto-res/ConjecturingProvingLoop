

theorem P2_nonempty_iff_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A.Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hA
    rcases hA with ⟨x, hxA⟩
    have hxIntCl : x ∈ interior (closure (interior A)) := hP2 hxA
    by_cases hInt : (interior A).Nonempty
    · exact hInt
    · -- If `interior A` were empty, we would derive a contradiction.
      have hIntEq : interior A = (∅ : Set X) :=
        Set.not_nonempty_iff_eq_empty.1 hInt
      have hClIntEq : closure (interior A) = (∅ : Set X) := by
        simpa [hIntEq, closure_empty]
      have hIntClEq : interior (closure (interior A)) = (∅ : Set X) := by
        simpa [hClIntEq, interior_empty]
      have hFalse : False := by
        simpa [hIntClEq] using hxIntCl
      exact False.elim hFalse
  · intro hInt
    exact hInt.mono interior_subset