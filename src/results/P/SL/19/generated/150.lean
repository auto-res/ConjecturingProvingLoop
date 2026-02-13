

theorem Topology.nonempty_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hA_non
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  ·
    -- In this branch we have `interior A = ∅`.
    have hIntEq : interior A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hInt
    -- Choose a point `x ∈ A` using the non‐emptiness of `A`.
    rcases hA_non with ⟨x, hxA⟩
    -- `P2` tells us that `x` lies in `interior (closure (interior A))`.
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    -- But this set is empty, contradicting the membership of `x`.
    have : x ∈ (∅ : Set X) := by
      simpa [hIntEq, closure_empty, interior_empty] using hxInt
    cases this