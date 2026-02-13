

theorem closureInterior_union_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure (interior A) ∪ closure (interior B)) := by
  -- Each `closure (interior _)` individually satisfies `P1`.
  have hA : Topology.P1 (closure (interior A)) :=
    closureInterior_P1 (X := X) (A := A)
  have hB : Topology.P1 (closure (interior B)) :=
    closureInterior_P1 (X := X) (A := B)
  -- The union of two `P1` sets is again `P1`.
  exact
    Topology.P1_union (X := X)
      (A := closure (interior A)) (B := closure (interior B)) hA hB