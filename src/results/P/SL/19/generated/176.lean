

theorem Topology.frontier_eq_frontier_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) → frontier A = frontier (interior A) := by
  intro hP1
  have hClos : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hClosA, hNotIntA⟩
    have hClosInt : x ∈ closure (interior A) := by
      simpa [hClos] using hClosA
    have hNotIntInt : x ∉ interior (interior A) := by
      simpa [interior_interior] using hNotIntA
    exact And.intro hClosInt hNotIntInt
  · intro hx
    rcases hx with ⟨hClosInt, hNotIntInt⟩
    have hClosA : x ∈ closure A := by
      simpa [hClos] using hClosInt
    have hNotIntA : x ∉ interior A := by
      simpa [interior_interior] using hNotIntInt
    exact And.intro hClosA hNotIntA