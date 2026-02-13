

theorem P1_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Topology.P1 (A ×ˢ (Set.univ : Set Y)) → Topology.P1 A := by
  intro hProd
  dsimp [Topology.P1] at hProd
  dsimp [Topology.P1]
  intro x hxA
  classical
  have y : Y := Classical.arbitrary Y
  have h_mem_prod : (x, y) ∈ A ×ˢ (Set.univ : Set Y) := by
    exact And.intro hxA (Set.mem_univ y)
  have h_closure_mem : (x, y) ∈ closure (interior (A ×ˢ (Set.univ : Set Y))) :=
    hProd h_mem_prod
  have h_int_prod :
      interior (A ×ˢ (Set.univ : Set Y)) =
        interior A ×ˢ (Set.univ : Set Y) := by
    simpa using
      interior_prod_eq (s := A) (t := (Set.univ : Set Y))
  have h_closure_prod :
      closure (interior (A ×ˢ (Set.univ : Set Y))) =
        closure (interior A) ×ˢ (Set.univ : Set Y) := by
    calc
      closure (interior (A ×ˢ (Set.univ : Set Y)))
          = closure (interior A ×ˢ (Set.univ : Set Y)) := by
              simpa [h_int_prod]
      _ = closure (interior A) ×ˢ (Set.univ : Set Y) := by
              simpa using
                closure_prod_eq
                  (s := interior A) (t := (Set.univ : Set Y))
  have h_in_prod :
      (x, y) ∈ closure (interior A) ×ˢ (Set.univ : Set Y) := by
    simpa [h_closure_prod] using h_closure_mem
  exact (Set.mem_prod.1 h_in_prod).1