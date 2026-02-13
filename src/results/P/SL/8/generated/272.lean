

theorem P3_interiorClosure_inter_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    interior (closure A) ∩ A = A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    exact And.intro hxInt hxA