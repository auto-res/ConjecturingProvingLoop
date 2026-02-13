

theorem P1_iff_closureInterior_inter_self_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔ closure (interior A) ∩ A = A := by
  constructor
  · intro hP1
    exact closureInterior_inter_self_eq_self_of_P1 (A := A) hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hxA
    -- Using the assumed equality to place `x` in the required closure.
    have hxInter : x ∈ closure (interior (A : Set X)) ∩ A := by
      simpa [hEq] using hxA
    exact hxInter.1