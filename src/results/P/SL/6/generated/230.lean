

theorem closureInterior_inter_self_eq_self_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → (closure (interior A) ∩ A = A) := by
  intro hP1
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxA
    have hxCl : x ∈ closure (interior (A : Set X)) := hP1 hxA
    exact And.intro hxCl hxA