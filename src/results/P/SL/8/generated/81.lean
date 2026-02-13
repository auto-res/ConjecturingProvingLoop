

theorem P1_nonempty_iff_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A.Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hA
    by_contra hIntEmpty
    have hIntEq : interior A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hIntEmpty
    have hClInt : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty]
    rcases hA with ⟨x, hxA⟩
    have hxCl : x ∈ closure (interior A) := hP1 hxA
    simpa [hClInt] using hxCl
  · intro hInt
    exact hInt.mono interior_subset