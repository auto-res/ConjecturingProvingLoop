

theorem Topology.closureInterior_inter_closed_eq_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ∩ A = closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hxA : x ∈ A :=
      (Topology.closureInterior_subset_of_isClosed (A := A) hA) hx
    exact ⟨hx, hxA⟩